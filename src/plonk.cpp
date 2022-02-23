#include <sys/types.h>
#include <sys/stat.h>
#include <fcntl.h>

#include <sodium.h>
#include "../depends/xkcp/Standalone/CompactFIPS202/C/Keccak-more-compact.c"

#include <iostream>
#include <iomanip>

#include "logger.hpp"
#include "plonk.hpp"

using namespace CPlusPlusLogging;

#define ASSERT(cond,msg) if(!(cond)) { throw std::runtime_error(std::string(msg) + " at " __FILE__ ":" + std::to_string(__LINE__)); }

namespace Plonk {

template <typename Engine>
std::unique_ptr<::Prover<Engine>> makeProver(
    u_int32_t nVars, 
    u_int32_t nPublic, 
    u_int32_t domainSize,
    u_int32_t nConstrains,
    u_int32_t nAdditions,
    u_int32_t lPolsSize,
    u_int32_t nPtau,
    void *k1,
    void *k2,
    void *qm,
    void *ql,
    void *qr,
    void *qo,
    void *qc,
    void *additions,
    void *mapA,
    void *mapB,
    void *mapC,
    void *QM,
    void *QL,
    void *QR,
    void *QO,
    void *QC,
    void *lPols,
    void *ptau,
    void *sigmas
) {
    Prover<Engine> *p = new Prover<Engine>(
        Engine::engine, 
        nVars, 
        nPublic, 
        domainSize, 
        nConstrains,
        nAdditions,
        lPolsSize,
        nPtau,
        *(typename Engine::FrElement *) k1,
        *(typename Engine::FrElement *) k2,
        *(typename Engine::FrElement *) qm,
        *(typename Engine::FrElement *) ql,
        *(typename Engine::FrElement *) qr,
        *(typename Engine::FrElement *) qo,
        *(typename Engine::FrElement *) qc,
        (Additional<Engine> *)((uint64_t) additions),
        (u_int32_t *)mapA,
        (u_int32_t *)mapB,
        (u_int32_t *)mapC,
        (typename Engine::FrElement *) QM,
        (typename Engine::FrElement *) QL,
        (typename Engine::FrElement *) QR,
        (typename Engine::FrElement *) QO,
        (typename Engine::FrElement *) QC,        
        (typename Engine::FrElement *) lPols,        
        (typename Engine::G1PointAffine *)ptau,
        (typename Engine::FrElement *) sigmas
    );
    return std::unique_ptr< Prover<Engine> >(p);
}

template <typename Engine>
std::unique_ptr<::Proof<Engine>> Prover<Engine>::prove(FrElement *wtns) {
    FrElements internalWitness(nAdditions);

    try {
        LOG_TRACE("Plonk - load widness");
        loadWitness(wtns);

        LOG_TRACE("Plonk - calculate additions");
        calculateAdditions();
        
        LOG_TRACE("Plonk - Round 1");
        round1();

        LOG_TRACE("Plonk - Round 2");
        round2();

        LOG_TRACE("Plonk - Round 3");
        round3();

        LOG_TRACE("Plonk - Round 4");
        round4();

        LOG_TRACE("Plonk - Round 5");
        round5();
    } 
    catch (const std::exception &e) {
        std::cerr << "EXCEPTION: " << e.what() << "\n";
    }

    LOG_TRACE("Plonk - compose proof");
    Proof<Engine> *p = new Proof<Engine>(Engine::engine);
    composeProof(*p);

    return std::unique_ptr<Proof<Engine>>(p);
}

template <typename Engine>
void Prover<Engine>::loadSigmas(FrElement *sigmas) 
{
    loadFrElements(sigmaExt, sigmas, domainSize, domainSize * 4);
    loadFrElements(sigmaExt, sigmas, domainSize*6, domainSize * 4, domainSize * 4);
    loadFrElements(sigmaExt, sigmas, domainSize*11, domainSize * 4, domainSize * 8);

    loadFrElements(polS1, sigmas, 0, domainSize);
    loadFrElements(polS2, sigmas, domainSize * 5, domainSize);
    loadFrElements(polS3, sigmas, domainSize * 10, domainSize);
}

template <typename Engine>
void Prover<Engine>::loadFrElements(FrElements &destination, const FrElement *source, u_int32_t offset, u_int32_t count, u_int32_t seek) 
{
    if (destination.size() < (seek + count)) {
        destination.resize(seek + count);
    }
    
    #pragma omp parallel for
    for (auto i = 0; i < count; ++i) {
        destination[seek + i] = source[offset + i];
    }
}

template <typename Engine>
void Prover<Engine>::loadWitness(FrElement *wtns) 
{
    size_t nWitness = nVars - nAdditions;
    witness.resize(nWitness);

    #pragma omp parallel for
    for (int i = 1; i < nWitness; ++i) {
        witness[i] = wtns[i];
    }

    // First element in plonk is not used and can be any value. (But always the same).
    // We set it to zero to go faster in the exponentiations.
    witness[0] = E.fr.zero();
}

template <typename Engine>
void Prover<Engine>::round1 ( void ) 
{
    generateRandomBlindingScalars(randomBlindings);

    setMontgomeryPolynomialFromWitnessMap(A, mapA);
    polA.assign(A.begin(), A.end());

    setMontgomeryPolynomialFromWitnessMap(B, mapB);
    polB = B;

    setMontgomeryPolynomialFromWitnessMap(C, mapC);
    polC = C;

    polA4 = buildPolynomial(polA, randomBlindings, {2, 1});
    polB4 = buildPolynomial(polB, randomBlindings, {4, 3});
    polC4 = buildPolynomial(polC, randomBlindings, {6, 5});

    proofA = expTau(polA);
    proofB = expTau(polB);
    proofC = expTau(polC);
}

template <typename Engine>
void Prover<Engine>::round2 ( void ) 
{
    calculateChallengeBeta();
    calculateChallengeGamma();
    computePermutationPolynomialZ();
}

template <typename Engine>
void Prover<Engine>::round3 ( void ) 
{
    calculateChallengeAlpha();
    settingZn();
    computeQuotientPolynomial();
}

template <typename Engine>
typename Engine::G1Point Prover<Engine>::expTau ( FrElements &polynomial ) 
{
    G1P value;
    FrElements pol = polynomial;
    polynomialFromMontgomery(pol);

    E.g1.multiMulByScalar(value, ptau.data(), (uint8_t *)pol.data(), sizeof(pol[0]), pol.size());
    return value;
}

template <typename Engine>
void Prover<Engine>::generateRandomBlindingScalars ( FrElements &randomBlindings ) 
{
    // 0 index not used

    randomBlindings[0] = E.fr.zero();
    for (int i=0; i<9; ++i) {
        randombytes_buf((void *)&(randomBlindings[i].v[0]), sizeof(randomBlindings[0])-1);
        randombytes_buf((void *)&(randomBlindings[i].v[0]), sizeof(randomBlindings[0])-1);
    }    
}

template <typename Engine>
typename Prover<Engine>::FrElements Prover<Engine>::buildPolynomial ( FrElements &polynomial, FrElements &randomBlindings, std::vector<u_int32_t> randomBlindingIndexs ) 
{
    evaluationsToCoefficients(polynomial);

    FrElements polynomial4T = extendPolynomial(polynomial, polynomial.size() * 4);
    coefficientsToEvaluations(polynomial4T);

    polynomial.resize(polynomial.size() + randomBlindingIndexs.size());
    u_int32_t nthIndex = domainSize;

    // (b1X + b2) ZH(X) => (b1X + b2) (X^n - 1) = b2X^n - b2 + b1X^n+1 - b1X
    for (u_int32_t index = 0; index < randomBlindingIndexs.size(); ++index) {
        // b2X^n , b1X^n+1, ...
        E.fr.add(polynomial[nthIndex + index], 
                 polynomial[nthIndex + index], 
                 randomBlindings[randomBlindingIndexs[index]]);

        // -b2, -b1X, ...
        E.fr.sub(polynomial[index], 
                 polynomial[index], 
                 randomBlindings[randomBlindingIndexs[index]]);
    }

    return polynomial4T;
}

template <typename Engine>
void Prover<Engine>::computePermutationPolynomialZ ( void )
{   
    u_int32_t n = domainSize * 4;
    FrElement denominator, numerator; 
    FrElements betaW(n);

    FrElement w = E.fr.one();
    FrElements numerators(domainSize);
    FrElements denominators(domainSize);

    numerators[0] = E.fr.one();
    denominators[0] = E.fr.one();

    for (int index = 0 ; index < domainSize; index++) {
        E.fr.mul(betaW[index], chBeta, w);
        E.fr.mul(w, w, wFactor);
    }

    for (int index = 0 ; index < domainSize; index++) {
        // computePermutationPolynomialZLoop(index, n, numerator, denominator, betaW);
        computePermutationPolynomialZLoop(index, n, numerators[(index+1) % domainSize], numerators[(index+1) % domainSize], betaW[index]);
    }

    #pragma omp parallel for
    for (int index = 0 ; index < domainSize; index++) {
        E.fr.mul(numerators[(index+1) % domainSize], numerators[index], numerators[(index+1) % domainSize]);
        E.fr.mul(denominators[(index+1) % domainSize], denominators[index], denominators[(index+1) % domainSize]);
    }

    calculateInverses(denominators);  

    multiplicateElements(numerators, numerators, denominators);    

    ASSERT(E.fr.eq(numerators[0], E.fr.one()), "Copy Constraints does not match");

    polZ = numerators;
    polZ4 = buildPolynomial(polZ, randomBlindings, {9, 8, 7});
    proofZ = expTau(polZ);
}

template <typename Engine>
void Prover<Engine>::computePermutationPolynomialZLoop ( int index, int n, FrElement &numerator, FrElement &denominator, const FrElement &betaW ) 
{
    FrElement aux;
    
    E.fr.add(numerator, A[index], betaW);
    E.fr.add(numerator, numerator, chGamma);

    E.fr.mul(aux, k1, betaW);
    E.fr.add(aux, aux, B[index]);
    E.fr.add(aux, aux, chGamma);
    E.fr.mul(numerator, numerator, aux);

    E.fr.mul(aux, k2, betaW);
    E.fr.add(aux, aux, C[index]);
    E.fr.add(aux, aux, chGamma);
    E.fr.mul(numerator, numerator, aux);

    // get on out of 4 to recover the evaluations before extending 4. For example:
    // [r1, r2] => [r1, r1.5, r2, r2.5] => [r1, r1.25, r1.5, r2, r2.25, r2.5, r2.75]
    // on positions 0 and 4 are original roots.

    // _w(j) + sigma(j) * chBeta + chGamma
    E.fr.mul(denominator, sigmaExt[index*4], chBeta);
    E.fr.add(denominator, denominator, A[index]);
    E.fr.add(denominator, denominator, chGamma);

    // _w(n+j) + sigma(n+j) * chBeta + chGamma
    E.fr.mul(aux, sigmaExt[n + index*4], chBeta);
    E.fr.add(aux, aux, B[index]);
    E.fr.add(aux, aux, chGamma);
    E.fr.mul(denominator, denominator, aux);

    // _w(2n+j) + sigma(2n + j) * chBeta + chGamma
    E.fr.mul(aux, sigmaExt[2*n + index*4], chBeta);
    E.fr.add(aux, aux, C[index]);
    E.fr.add(aux, aux, chGamma);
    E.fr.mul(denominator, denominator, aux);
}

template <typename Engine>
void Prover<Engine>::mul2 ( FrElement &r, FrElement &rz, const FrElement &a, const FrElement &b, 
                const FrElement &ap, const FrElement &bp, int64_t p ) 
{
    const FrElement a_b = E.fr.mul(a,b);
    const FrElement a_bp = E.fr.mul(a,bp);
    const FrElement ap_b = E.fr.mul(ap,b);
    const FrElement ap_bp = E.fr.mul(ap,bp);

    r = a_b;

    auto a0 = E.fr.add(a_bp, ap_b);
    auto a1 = ap_bp;

    rz = a0;
    if (p >= 0) {
        rz = E.fr.add(rz, E.fr.mul(Z1[p], a1));
    }
}

template <typename Engine>
void Prover<Engine>::mul4 ( FrElement &r, FrElement &rz, const FrElement &a, const FrElement &b, 
                const FrElement &c, const FrElement &d, const FrElement &ap, const FrElement &bp, 
                const FrElement &cp, const FrElement &dp, int64_t p ) 
{
    const FrElement a_b = E.fr.mul(a,b);
    const FrElement a_bp = E.fr.mul(a,bp);
    const FrElement ap_b = E.fr.mul(ap,b);
    const FrElement ap_bp = E.fr.mul(ap,bp);

    const FrElement c_d = E.fr.mul(c,d);
    const FrElement c_dp = E.fr.mul(c,dp);
    const FrElement cp_d = E.fr.mul(cp,d);
    const FrElement cp_dp = E.fr.mul(cp,dp);

    r = E.fr.mul(a_b, c_d);

    FrElement a0 = E.fr.mul(ap_b, c_d);
    a0 = E.fr.add(a0, E.fr.mul(a_bp, c_d));
    a0 = E.fr.add(a0, E.fr.mul(a_b, cp_d));
    a0 = E.fr.add(a0, E.fr.mul(a_b, c_dp));

    FrElement a1 = E.fr.mul(ap_bp, c_d);
    a1 = E.fr.add(a1, E.fr.mul(ap_b, cp_d));
    a1 = E.fr.add(a1, E.fr.mul(ap_b, c_dp));
    a1 = E.fr.add(a1, E.fr.mul(a_bp, cp_d));
    a1 = E.fr.add(a1, E.fr.mul(a_bp, c_dp));
    a1 = E.fr.add(a1, E.fr.mul(a_b, cp_dp));

    FrElement a2 = E.fr.mul(a_bp, cp_dp);
    a2 = E.fr.add(a2, E.fr.mul(ap_b, cp_dp));
    a2 = E.fr.add(a2, E.fr.mul(ap_bp, c_dp));
    a2 = E.fr.add(a2, E.fr.mul(ap_bp, cp_d));

    FrElement a3 = E.fr.mul(ap_bp, cp_dp);

    rz = a0;
    if (p >= 0) {
        rz = E.fr.add(rz, E.fr.mul(Z1[p], a1));
        rz = E.fr.add(rz, E.fr.mul(Z2[p], a2));
        rz = E.fr.add(rz, E.fr.mul(Z3[p], a3));
    }
}

template <typename Engine>
void Prover<Engine>::computeQuotientPolynomial ( void )
{   
    int domainSize4 = domainSize * 4;
    FrElements _T(domainSize * 4);
    FrElements _Tz(domainSize * 4);
    FrElement wFactorPlus2 = fft->root(domainPower+2, 1);

    FrElements w(domainSize4);
    w[0] = E.fr.one();
    for (u_int64_t i = 1; i < domainSize4; ++ i) {
        E.fr.mul(w[i], w[i-1], wFactorPlus2);        
    }

    #pragma omp parallel for
    for (u_int64_t i = 0; i < domainSize4; ++ i) {
        auto a = polA4[i];
        auto b = polB4[i];
        auto c = polC4[i];
        auto z = polZ4[i];
        auto zw = polZ4[(i+4*domainSize+4) % (domainSize*4)];
        auto qm = polQm4[i];
        auto ql = polQl4[i];
        auto qr = polQr4[i];
        auto qo = polQo4[i];
        auto qc = polQc4[i];
        auto s1 = sigmaExt[i];
        auto s2 = sigmaExt[domainSize*4 + i];
        auto s3 = sigmaExt[domainSize*8 + i];
        auto ap = E.fr.add(randomBlindings[2], E.fr.mul(randomBlindings[1], w[i]));
        auto bp = E.fr.add(randomBlindings[4], E.fr.mul(randomBlindings[3], w[i]));
        auto cp = E.fr.add(randomBlindings[6], E.fr.mul(randomBlindings[5], w[i]));
        auto w2 = E.fr.square(w[i]);
        auto zp = E.fr.add(E.fr.add(E.fr.mul(randomBlindings[7], w2), E.fr.mul(randomBlindings[8], w[i])), randomBlindings[9]);
        auto wW = E.fr.mul(w[i], wFactor);
        auto wW2 = E.fr.square(wW);
        auto zWp = E.fr.add(E.fr.add(E.fr.mul(randomBlindings[7], wW2), E.fr.mul(randomBlindings[8], wW)), randomBlindings[9]);

        auto pl = E.fr.zero();
        for (u_int64_t j = 0; j < nPublic; ++j) {
            pl = E.fr.sub(pl, E.fr.mul(lPols[j * 5 * domainSize + domainSize + i], A[j]));
        }

        FrElement e1, e1z;
        mul2(e1, e1z, a, b, ap, bp, i%4);
        e1 = E.fr.mul(e1, qm);
        e1z = E.fr.mul(e1z, qm);

        e1 = E.fr.add(e1, E.fr.mul(a, ql));
        e1z = E.fr.add(e1z, E.fr.mul(ap, ql));

        e1 = E.fr.add(e1, E.fr.mul(b, qr));
        e1z = E.fr.add(e1z, E.fr.mul(bp, qr));

        e1 = E.fr.add(e1, E.fr.mul(c, qo));
        e1z = E.fr.add(e1z, E.fr.mul(cp, qo));

        e1 = E.fr.add(e1, pl);
        e1 = E.fr.add(e1, qc);

        FrElement betaW = E.fr.mul(chBeta, w[i]);
        FrElement e2a = E.fr.add(a, betaW);
        e2a = E.fr.add(e2a, chGamma);

        FrElement e2b = E.fr.add(b, E.fr.mul(betaW, k1));
        e2b = E.fr.add(e2b, chGamma);

        FrElement e2c = c;
        e2c = E.fr.add(e2c, E.fr.mul(betaW, k2));
        e2c = E.fr.add(e2c, chGamma);

        FrElement e2d = z;

        FrElement e2;
        FrElement e2z;
        
        mul4(e2, e2z, e2a, e2b, e2c, e2d, ap, bp, cp, zp, i%4);
        e2 = E.fr.mul(e2, chAlpha);
        e2z = E.fr.mul(e2z, chAlpha);

        FrElement e3a = a;
        e3a = E.fr.add(e3a, E.fr.mul(chBeta, s1));
        e3a = E.fr.add(e3a, chGamma);

        FrElement e3b = b;
        e3b = E.fr.add(e3b, E.fr.mul(chBeta,s2));
        e3b = E.fr.add(e3b, chGamma);

        FrElement e3c = c;
        e3c = E.fr.add(e3c, E.fr.mul(chBeta,s3));
        e3c = E.fr.add(e3c, chGamma);

        FrElement e3d = zw;
        FrElement e3;
        FrElement e3z;
        mul4(e3, e3z, e3a, e3b, e3c, e3d, ap, bp, cp, zWp, i%4);

        e3 = E.fr.mul(e3, chAlpha);
        e3z = E.fr.mul(e3z, chAlpha);

        FrElement e4 = E.fr.sub(z, E.fr.one());
        e4 = E.fr.mul(e4, lPols[domainSize + i]);
        e4 = E.fr.mul(e4, E.fr.mul(chAlpha, chAlpha));

        FrElement e4z = E.fr.mul(zp, lPols[domainSize +i]);
        e4z = E.fr.mul(e4z, E.fr.mul(chAlpha, chAlpha));

        FrElement e = E.fr.add(E.fr.sub(E.fr.add(e1, e2), e3), e4);
        FrElement ez = E.fr.add(E.fr.sub(E.fr.add(e1z, e2z), e3z), e4z);

        _T[i] = e;
        _Tz[i] = ez;
    }

    evaluationsToCoefficients(_T);

    #pragma omp parallel for
    for (u_int64_t i = 0; i < domainSize; ++i) {
        _T[i] = E.fr.neg(_T[i]);
    }

    for (u_int64_t i = domainSize; i < domainSize4; ++i) {
        _T[i] = E.fr.sub(_T[ i - domainSize ], _T[i]);
        if (i > (domainSize * 3 - 4)) {
            ASSERT(E.fr.isZero(_T[i]), "T polynomial is not divisible");
        }
    }
    evaluationsToCoefficients(_Tz);

    #pragma omp parallel for
    for (u_int64_t i = 0; i < domainSize4; ++i) {
        if (i > (domainSize*3+5) ) {
            stringstream ss;
            ss << "Tz Polynomial is not well calculated Tz[" << i << "] != 0  domainSize:" << domainSize <<  " domainSize*3+5:" << (domainSize*3+5);
            ASSERT(E.fr.isZero(_Tz[i]), ss.str());
        } 
        else {
            _T[i] = E.fr.add(_T[i], _Tz[i]);
        }
    }
    
    polT.assign(_T.begin(), _T.begin() + (domainSize * 3 + 6));

    FrElements _polTpart(_T.begin(), _T.begin() + domainSize);
    proofT1 = expTau(_polTpart);

    _polTpart.assign(_T.begin() + domainSize , _T.begin() + domainSize*2);
    proofT2 = expTau(_polTpart);

    _polTpart.assign(_T.begin() + domainSize * 2, _T.begin() + (domainSize * 3 + 6));
    proofT3 = expTau(_polTpart);
} 

template <typename Engine>
typename Prover<Engine>::FrElement Prover<Engine>::evaluatePolynomial( const FrElements &pol, const FrElement &x )
{
    // TODO Review, original code check only if n == 0, but n must be at least 2
    if (pol.size() < 2) return E.fr.zero();

    FrElement res = pol.back();
    for (int64_t i = pol.size() - 2; i >= 0; i--) {
        res = E.fr.add(E.fr.mul(res, x), pol[i]);
    }
    return res;
}

template <typename Engine>
void Prover<Engine>::round4( void ) 
{
    calculateChallengeXi();

    proofEvalA = evaluatePolynomial(polA, chXi);
    proofEvalB = evaluatePolynomial(polB, chXi);
    proofEvalC = evaluatePolynomial(polC, chXi);
    proofEvalS1 = evaluatePolynomial(polS1, chXi);
    proofEvalS2 = evaluatePolynomial(polS2, chXi);
    proofEvalT = evaluatePolynomial(polT, chXi);
    proofEvalZw = evaluatePolynomial(polZ, E.fr.mul(chXi, wFactor));

    FrElement coef_ab = E.fr.mul(proofEvalA, proofEvalB);   
    FrElement e2a = proofEvalA;
    FrElement betaxi = E.fr.mul(chBeta, chXi);

    e2a = E.fr.add( e2a, betaxi);
    e2a = E.fr.add( e2a, chGamma);

    FrElement e2b = proofEvalB;
    e2b = E.fr.add( e2b, E.fr.mul(betaxi, k1));
    e2b = E.fr.add( e2b, chGamma);

    FrElement e2c = proofEvalC;
    e2c = E.fr.add( e2c, E.fr.mul(betaxi, k2));
    e2c = E.fr.add( e2c, chGamma);

    FrElement e2 = E.fr.mul(E.fr.mul(E.fr.mul(e2a, e2b), e2c), chAlpha);
    
    FrElement e3a = proofEvalA;
    e3a = E.fr.add( e3a, E.fr.mul(chBeta, proofEvalS1));
    e3a = E.fr.add( e3a, chGamma);

    FrElement e3b = proofEvalB;
    e3b = E.fr.add( e3b, E.fr.mul(chBeta, proofEvalS2));
    e3b = E.fr.add( e3b, chGamma);

    FrElement e3 = E.fr.mul(e3a, e3b);
    e3 = E.fr.mul(e3, chBeta);
    e3 = E.fr.mul(e3, proofEvalZw);
    e3 = E.fr.mul(e3, chAlpha);
    
    xim = chXi;
    for (u_int64_t i=0; i<domainPower; i++) {
        xim = E.fr.mul(xim, xim);
    }

    FrElement eval_l1;
    E.fr.div(eval_l1,
        E.fr.sub(xim, E.fr.one()),
        E.fr.mul(E.fr.sub(chXi, E.fr.one()), domainSize)
    );

    FrElement e4 = E.fr.mul(eval_l1, E.fr.mul(chAlpha, chAlpha));
    FrElement coefs3 = e3;
    FrElement coefz = E.fr.add(e2, e4);

    polR.resize(domainSize + 3);

    #pragma omp parallel for
    for (u_int64_t i = 0; i < (domainSize+3); i++) {
        FrElement v = E.fr.mul(coefz, polZ[i]);
        if (i < domainSize) {
            v = E.fr.add(v, E.fr.mul(coef_ab, polQm[i]));
            v = E.fr.add(v, E.fr.mul(proofEvalA, polQl[i]));
            v = E.fr.add(v, E.fr.mul(proofEvalB, polQr[i]));
            v = E.fr.add(v, E.fr.mul(proofEvalC, polQo[i]));
            v = E.fr.add(v, polQc[i]);
            v = E.fr.sub(v, E.fr.mul(coefs3, polS3[i]));
        }
        polR[i] = v;
    }
    proofEvalR = evaluatePolynomial(polR, chXi);
}

template <typename Engine>
void Prover<Engine>::settingZn ( void )
{   
    FrElement w2 = fft->root(2, 1);

    Z1[0] = E.fr.zero();
    Z1[1] = E.fr.add(-1, w2);
    Z1[2] = E.fr.set(-2);
    Z1[3] = E.fr.sub(-1, w2);

    Z2[0] = E.fr.zero();
    Z2[1] = E.fr.add(0, E.fr.mul(-2, w2));
    Z2[2] = E.fr.set(4);
    Z2[3] = E.fr.sub(0, E.fr.mul(-2, w2));

    Z3[0] = E.fr.zero();
    Z3[1] = E.fr.add(2, E.fr.mul(2, w2));
    Z3[2] = E.fr.set(-8);
    Z3[3] = E.fr.sub(2, E.fr.mul(2, w2));
}


template <typename Engine>
void Prover<Engine>::round5( void ) 
{
    calculateChallengeV();

    u_int64_t extraDomainSize = domainSize + 6;
    FrElements polWxi(extraDomainSize);
    FrElement xi2m = E.fr.mul(xim, xim);

    #pragma omp parallel for
    for (u_int64_t i = 0; i < extraDomainSize; i++) {
        FrElement w = E.fr.zero();
        w = E.fr.add(w, E.fr.mul(xi2m, polT[domainSize * 2 + i]));

        if (i < domainSize+3) {
            w = E.fr.add(w, E.fr.mul(chV[1],  polR[i]));
        }

        if (i < domainSize+2) {
            // w = w + chV[2] * polA[i] + chV[3] * polB[i] + chV[4] * polC[i];
            w = E.fr.add(w, E.fr.mul(chV[2],  polA[i]));
            w = E.fr.add(w, E.fr.mul(chV[3],  polB[i]));
            w = E.fr.add(w, E.fr.mul(chV[4],  polC[i]));
        }
        
        if (i < domainSize) {
            // w = w + polT[i] + xim * polT[n + i] + chV[5] * polS1[i] + chV[6] * polS2[i];
            w = E.fr.add(w, polT[i]);
            w = E.fr.add(w, E.fr.mul(xim, polT[domainSize + i]));
            w = E.fr.add(w, E.fr.mul(chV[5], polS1[i]));
            w = E.fr.add(w, E.fr.mul(chV[6], polS2[i]));
        }

        polWxi[i] = w;
    }

    polWxi[0] = E.fr.sub(polWxi[0], proofEvalT);
    polWxi[0] = E.fr.sub(polWxi[0], E.fr.mul(chV[1], proofEvalR));
    polWxi[0] = E.fr.sub(polWxi[0], E.fr.mul(chV[2], proofEvalA));
    polWxi[0] = E.fr.sub(polWxi[0], E.fr.mul(chV[3], proofEvalB));
    polWxi[0] = E.fr.sub(polWxi[0], E.fr.mul(chV[4], proofEvalC));
    polWxi[0] = E.fr.sub(polWxi[0], E.fr.mul(chV[5], proofEvalS1));
    polWxi[0] = E.fr.sub(polWxi[0], E.fr.mul(chV[6], proofEvalS2));    

    polWxi = div1(polWxi, chXi);

    proofWxi = expTau(polWxi);

    FrElements polWxiw(polZ.begin(), polZ.begin() + domainSize + 3);

    polWxiw[0] = E.fr.sub(polWxiw[0], proofEvalZw);

    polWxiw = div1(polWxiw, E.fr.mul(chXi, wFactor));

    proofWxiw = expTau(polWxiw);
}

template <typename Engine>
void Prover<Engine>::composeProof ( Proof<Engine> &proof )
{
    E.g1.copy(proof.A, proofA);
    E.g1.copy(proof.B, proofB);
    E.g1.copy(proof.C, proofC);
    E.g1.copy(proof.Z, proofZ);

    E.g1.copy(proof.T1, proofT1);
    E.g1.copy(proof.T2, proofT2);
    E.g1.copy(proof.T3, proofT3);

    proof.evalA = proofEvalA;
    proof.evalB = proofEvalB;
    proof.evalC = proofEvalC;
    proof.evalS1 = proofEvalS1;
    proof.evalS2 = proofEvalS2;
    proof.evalZw = proofEvalZw;
    proof.evalR = proofEvalR;
    proof.evalT = proofEvalT;

    E.g1.copy(proof.Wxi, proofWxi);
    E.g1.copy(proof.Wxiw, proofWxiw);
}

template <typename Engine>
typename Prover<Engine>::FrElements Prover<Engine>::div1(const FrElements &pol, const FrElement &divisor) 
{
    int64_t n = pol.size();
    FrElements res(n);
    res[n-1] = E.fr.zero();
    res[n-2] = pol[n-1];
    for (int64_t i = n - 3; i >= 0; --i) {
        res[i] = E.fr.add(pol[i+1], E.fr.mul(divisor, res[i+1]));
    }
    ASSERT(E.fr.eq(pol[0], E.fr.mul(E.fr.neg(divisor), res[0])), "Polinomial does not divide");
    return res;
}

template <typename Engine>
void Prover<Engine>::multiplicateElements(FrElements &destination, FrElements &a, FrElements &b)
{
    u_int64_t elementsCount = a.size();
    destination.resize(elementsCount);

    #pragma omp parallel for
    for (u_int64_t index = 0; index < elementsCount; index++)
    {
        E.fr.mul(destination[index], a[index], b[index]);
    }
}

template <typename Engine>
void Prover<Engine>::calculateInverses(FrElements &elements)
{
    // Calculate products: a, ab, abc, abcd, ...
    u_int64_t elementsCount = elements.size();
    FrElements products(elementsCount);

    products[0] = elements[0];
    for (u_int64_t index = 1; index < elementsCount; index++)
    {
        E.fr.mul(products[index], products[index-1], elements[index]);
    }

    // Calculate inverses: 1/a, 1/ab, 1/abc, 1/abcd, ...
    FrElements inverses(elementsCount);
    E.fr.inv(inverses[elementsCount - 1], products[elementsCount - 1]);
    for (u_int64_t index = elementsCount - 1; index > 0; index--)
    {
        E.fr.mul(inverses[index - 1], inverses[index], elements[index]);
    }

    elements[0] = inverses[0];
    for (u_int64_t index = 1; index < elementsCount; index++)
    {
        E.fr.mul(elements[index], inverses[index], products[index - 1]);
    }
}

template <typename Engine>
typename Prover<Engine>::FrElements Prover<Engine>::extendPolynomial ( const FrElements &polynomial, u_int32_t size ) 
{
    FrElements polynomial4T(size);
    #pragma omp parallel for
    for (u_int32_t index = 0; index < size; ++index) {
        polynomial4T[index] = (index < polynomial.size()) ? polynomial[index] : E.fr.zero();
        // polynomial4T[index] = polynomial[index % polynomial.size()];
    }
    return polynomial4T;
}

template <typename Engine>
inline void Prover<Engine>::evaluationsToCoefficients ( FrElements &polynomial ) 
{
    fft->ifft(polynomial.data(), polynomial.size());
    // fft->ifft(polynomial.data(), domainSize);
}

template <typename Engine>
inline void Prover<Engine>::coefficientsToEvaluations ( FrElements &polynomial ) 
{
    fft->fft(polynomial.data(), polynomial.size());
    // fft->fft(polynomial.data(), domainSize);
}

template <typename Engine>
void Prover<Engine>::setMontgomeryPolynomialFromWitnessMap ( FrElements &polynomial, u_int32_t *map) 
{
    #pragma omp parallel for
    for (int i=0; i<nConstrains; ++i) {
        FrElement aux;
        
        aux = getWitness(map[i]);
        E.fr.toMontgomery(polynomial[i], aux);
    }
}

template <typename Engine>
void Prover<Engine>::polynomialToMontgomery ( FrElements &polynomial ) 
{
    #pragma omp parallel for
    for (u_int32_t index=0; index<polynomial.size(); ++index) {
        E.fr.toMontgomery(polynomial[index], polynomial[index]);
    }
}

template <typename Engine>
void Prover<Engine>::polynomialFromMontgomery ( FrElements &polynomial ) 
{
    #pragma omp parallel for
    for (u_int32_t index=0; index<polynomial.size(); ++index) {
        E.fr.fromMontgomery(polynomial[index], polynomial[index]);
    }
}

template <typename Engine>
std::string Proof<Engine>::toJsonStr() 
{
    std::stringstream ss;
    
    ss << ("{\n");
    
    put(ss, "A", A);
    put(ss, "B", B);
    put(ss, "C", C);
    put(ss, "Z", Z);
    put(ss, "T1", T1);
    put(ss, "T2", T2);
    put(ss, "T3", T3);
    put(ss, "eval_a", evalA);
    put(ss, "eval_b", evalB);
    put(ss, "eval_c", evalC);
    put(ss, "eval_s1", evalS1);
    put(ss, "eval_s2", evalS2);
    put(ss, "eval_zw", evalZw);
    put(ss, "eval_r", evalR);
    put(ss, "Wxi", Wxi);
    put(ss, "Wxiw", Wxiw);
    ss  << " \"protocol\": \"plonk\",\n"
        << " \"curve\": \"" << (std::is_base_of_v<AltBn128::Engine, Engine> ? "bn128":"unknown") << "\"\n"
        << "}\n";

    return ss.str();
}

template <typename Engine>
json Proof<Engine>::toJson() 
{
    json p;

    put(p, "A", A);
    put(p, "B", B);
    put(p, "C", C);
    put(p, "Z", Z);
    put(p, "T1", T1);
    put(p, "T2", T2);
    put(p, "T3", T3);
    put(p, "eval_a", evalA);
    put(p, "eval_b", evalB);
    put(p, "eval_c", evalC);
    put(p, "eval_s1", evalS1);
    put(p, "eval_s2", evalS2);
    put(p, "eval_zw", evalZw);
    put(p, "eval_r", evalR);
    put(p, "Wxi", Wxi);
    put(p, "Wxiw", Wxiw);

    p["protocol"] = "plonk";
    p["curve"] = (std::is_base_of_v<AltBn128::Engine, Engine> ? "bn128":"unknown");
    return p;
}

template <typename Engine>
void Proof<Engine>::put(json &p, const std::string &name, typename Engine::G1PointAffine &point)
{   
    p[name] = {};
    p[name].push_back(E.f1.toString(point.x));
    p[name].push_back(E.f1.toString(point.y));
    p[name].push_back("1");
}

template <typename Engine>
void Proof<Engine>::put(json &p, const std::string &name, typename Engine::FrElement &element)
{   
    p[name] = E.fr.toString(element);
}

template <typename Engine>
void Proof<Engine>::put(stringstream &ss, const std::string &name, typename Engine::G1PointAffine &point)
{
    ss << " \"" << name << "\": [\n  \"" << E.f1.toString(point.x) << "\",\n  \"" << E.f1.toString(point.y) << "\",\n  \"1\"\n ],\n";
}

template <typename Engine>
void Proof<Engine>::put(stringstream &ss, const std::string &name, typename Engine::FrElement &element)
{
    ss << " \"" << name << "\": \"" << E.fr.toString(element) << "\",\n";
}

template <typename Engine>
void Prover<Engine>::calculateAdditions(void) {

    for (u_int64_t i=0; i<nAdditions; i++) {
        FrElement aWitness, bWitness, ac_aw, bc_bw;

        aWitness = getWitness(additions[i].ai);
        bWitness = getWitness(additions[i].bi);
        // TODO verify indexs and inside additions
        E.fr.mul(
            ac_aw,
            additions[i].ac,
            aWitness
        );
        E.fr.mul(
            bc_bw,
            additions[i].bc,
            bWitness
        );
        E.fr.add(
            internalWitness[i],
            ac_aw,
            bc_bw
        );
    }
}

template <typename Engine>
typename Prover<Engine>::FrElement Prover<Engine>::getWitness(u_int32_t index)
{
    if (index < nVars - nAdditions) {
        return witness[index];
    }
    else if (index < nVars) {
        return internalWitness[index - (nVars - nAdditions)];
    }

    return E.fr.zero();
}


// TODO: this method should be inside the G1P class.

template <typename Engine>
u_int64_t Prover<Engine>::toRprBE(G1P &point, uint8_t *data, u_int64_t seek, u_int64_t size)
{
    u_int64_t bytes = E.g1.F.bytes() * 2;
    G1Pa p;

    E.g1.copy(p, point);

    if (E.g1.isZero(p)) {
        memset(data, 0, bytes);
        return 0;
    }
    bytes = E.g1.F.toRprBE(p.x, data + seek, size);
    bytes += E.g1.F.toRprBE(p.y, data + seek + bytes, size);
    return bytes;
}

template <typename Engine>
void Prover<Engine>::hashToFr(FrElement &element, u_int8_t *data, u_int64_t size)
{
    // Keccak keccak;
    // std::string hash = keccak(data, size, true);
    // E.fr.fromRprBE(element, (const u_int8_t*) hash.c_str(), 32);
    u_int8_t hash[32];
    Keccak(1088, 512, data, size, 0x01, hash, sizeof(hash));
    E.fr.fromRprBE(element, hash, sizeof(hash));
}

template <typename Engine>
void Prover<Engine>::calculateChallengeBeta(void)
{
    u_int8_t data[E.g1.F.N64 * 8 * 2 * 3];
    size_t bytes = 0;

    memset(data, 0, sizeof(data));

    bytes = toRprBE(proofA, data, 0, sizeof(data));
    bytes += toRprBE(proofB, data, bytes, sizeof(data));
    bytes += toRprBE(proofC, data, bytes, sizeof(data));

    hashToFr(chBeta, data, bytes);
}

template <typename Engine>
void Prover<Engine>::calculateChallengeGamma(void)
{
    u_int8_t data[E.fr.bytes()];
    size_t bytes = 0;

    bytes = E.fr.toRprBE(chBeta, data, sizeof(data));
    hashToFr(chGamma, data, bytes);
}

template <typename Engine>
void Prover<Engine>::calculateChallengeAlpha(void)
{
    u_int8_t data[E.fr.bytes() * 2];
    size_t bytes = 0;

    bytes = toRprBE(proofZ, data, 0, sizeof(data));
    hashToFr(chAlpha, data, bytes);
}

template <typename Engine>
void Prover<Engine>::calculateChallengeXi(void)
{
    u_int8_t data[E.g1.F.bytes() * 2 * 3];
    size_t bytes = 0;

    memset(data, 0, sizeof(data));

    bytes = toRprBE(proofT1, data, 0, sizeof(data));
    bytes += toRprBE(proofT2, data, bytes, sizeof(data));
    bytes += toRprBE(proofT3, data, bytes, sizeof(data));

    hashToFr(chXi, data, bytes);
}

template <typename Engine>
void Prover<Engine>::calculateChallengeV(void)
{
    u_int8_t data[E.fr.bytes() * 7];
    size_t bytes = 0;
    chV.resize(7);

    memset(data, 0, sizeof(data));

    bytes = E.fr.toRprBE(proofEvalA, data, sizeof(data));
    bytes += E.fr.toRprBE(proofEvalB, data + bytes, sizeof(data));
    bytes += E.fr.toRprBE(proofEvalC, data + bytes, sizeof(data));
    bytes += E.fr.toRprBE(proofEvalS1, data + bytes, sizeof(data));
    bytes += E.fr.toRprBE(proofEvalS2, data + bytes, sizeof(data));
    bytes += E.fr.toRprBE(proofEvalZw, data + bytes, sizeof(data));
    bytes += E.fr.toRprBE(proofEvalR, data + bytes, sizeof(data));

    hashToFr(chV[1], data, bytes);
    for (int i=2; i<=6; i++) {
        chV[i] = E.fr.mul(chV[i-1], chV[1]);
    }
}


} // namespace