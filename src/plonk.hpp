#ifndef __RAPIDSNARK__PLONK_H__
#define __RAPIDSNARK__PLONK_H__

#include <string>
#include <nlohmann/json.hpp>
using json = nlohmann::json;

#include "binfile_utils.hpp"
#include "fft.hpp"
#include "prover.hpp"
#include "proof.hpp"
#include "dump.hpp"

namespace Plonk {

    template <typename Engine>
    class Proof: public ::Proof<Engine> {
        Engine &E;
    public:
        // curve
        // protocol
        typename Engine::G1PointAffine A;
        typename Engine::G1PointAffine B;
        typename Engine::G1PointAffine C;
        typename Engine::G1PointAffine Z;

        typename Engine::G1PointAffine T1;
        typename Engine::G1PointAffine T2;
        typename Engine::G1PointAffine T3;

        typename Engine::FrElement evalA;
        typename Engine::FrElement evalB;
        typename Engine::FrElement evalC;
        typename Engine::FrElement evalS1;
        typename Engine::FrElement evalS2;
        typename Engine::FrElement evalZw;
        typename Engine::FrElement evalR;
        typename Engine::FrElement evalT;

        typename Engine::G1PointAffine Wxi;
        typename Engine::G1PointAffine Wxiw;

        Proof(Engine &_E) : E(_E) { };
        std::string toJsonStr();
        json toJson();
    protected:
        void put(json &p, const std::string &name, typename Engine::G1PointAffine &point);
        void put(json &p, const std::string &name, typename Engine::FrElement &element);
        void put(stringstream &ss, const std::string &name, typename Engine::G1PointAffine &point);
        void put(stringstream &ss, const std::string &name, typename Engine::FrElement &element);
    };


 #pragma pack(push, 1)
    template <typename Engine>
    struct Coef {
        u_int32_t m;
        u_int32_t c;
        u_int32_t s;
        typename Engine::FrElement coef;
    };
    template <typename Engine>
    struct Additional {
        u_int32_t ai;
        u_int32_t bi;
        typename Engine::FrElement ac;
        typename Engine::FrElement bc;
    };
#pragma pack(pop)

    template <typename Engine>
    class Prover: public ::Prover<Engine> {

        using FrElement = typename Engine::FrElement;
        using FrElements = vector<typename Engine::FrElement>;

        using G1Pa = typename Engine::G1PointAffine;
        using G1Pas = vector<typename Engine::G1PointAffine>;
        using G2Pa = typename Engine::G2PointAffine;
        using G2Pas = vector<typename Engine::G2PointAffine>;

        using G1P = typename Engine::G1Point;
        using G1Ps = vector<typename Engine::G1Point>;
        using G2P = typename Engine::G2Point;
        using G2Ps = vector<typename Engine::G2Point>;

        using FqElement = typename Engine::F1::Element;

        Engine &E;
        u_int32_t nVars;
        u_int32_t nPublic;
        u_int32_t domainSize;
        u_int32_t domainPower;
        u_int32_t nConstrains;
        u_int32_t nAdditions;

        FrElement k1;
        FrElement k2;

        // WARNING tiene dos elementos !! carga correcta !!! TODO
        FrElement qm;
        FrElement ql;
        FrElement qr;
        FrElement qo;
        FrElement qc;
        Additional<Engine> *additions;
        FrElements internalWitness;
        FrElements sigmaExt;
        FrElements polS1, polS2, polS3;
        G1Pas ptau;

        FrElement wFactor;

        u_int32_t *mapA;
        u_int32_t *mapB;
        u_int32_t *mapC;

        FrElements A;
        FrElements B;
        FrElements C;
        FrElements polA, polB, polC, polZ, polR;
        FrElements polA4, polB4, polC4, polZ4;
        FrElements polQm, polQl, polQr, polQo, polQc;
        FrElements polQm4, polQl4, polQr4, polQo4, polQc4;
        
        FrElements witness;
        FrElement chBeta;
        FrElement chGamma;
        FrElement chAlpha;
        FrElement chXi;
        FrElements chV;
        FrElement xim;
        
        FrElements randomBlindings;

        G1P proofA, proofB, proofC, proofZ, proofT1, proofT2, proofT3, proofWxi, proofWxiw;
        FrElement proofEvalA, proofEvalB, proofEvalC, proofEvalS1, proofEvalS2;
        FrElement proofEvalT, proofEvalZw, proofEvalR;

        FrElements polT;
        FrElements lPols;

        FrElement Z1[4];
        FrElement Z2[4];
        FrElement Z3[4];

        FFT<typename Engine::Fr> *fft;

        Dump::Dump<Engine> dump;
    public:
        Prover(
            Engine &_E, 
            u_int32_t _nVars, 
            u_int32_t _nPublic, 
            u_int32_t _domainSize, 
            u_int32_t _nConstrains,
            u_int32_t _nAdditions,      
            u_int32_t _lPolsSize,      
            u_int32_t _nPtau,
            typename Engine::FrElement _k1,
            typename Engine::FrElement _k2,
            typename Engine::FrElement &_qm,
            typename Engine::FrElement &_ql,
            typename Engine::FrElement &_qr,
            typename Engine::FrElement &_qo,
            typename Engine::FrElement &_qc,
            Additional<Engine> *_additions,
            u_int32_t *_mapA,
            u_int32_t *_mapB,
            u_int32_t *_mapC,
            typename Engine::FrElement *_QM,
            typename Engine::FrElement *_QL,
            typename Engine::FrElement *_QR,
            typename Engine::FrElement *_QO,
            typename Engine::FrElement *_QC,
            typename Engine::FrElement *_lPols,
            typename Engine::G1PointAffine *_ptau,
            typename Engine::FrElement *_sigmas
        ) : 
            E(_E), 
            nVars(_nVars),
            nPublic(_nPublic),
            domainSize(_domainSize),
            nConstrains(_nConstrains),
            nAdditions(_nAdditions),
            additions(_additions),
            mapA(_mapA),
            mapB(_mapB),
            mapC(_mapC),
            ptau(_ptau, _ptau + (_nPtau/sizeof(typename Engine::G1PointAffine))),
            A(_domainSize),
            B(_domainSize),
            C(_domainSize),
            randomBlindings(1+9),
            dump(_E)
        { 
            fft = new FFT<typename Engine::Fr>(domainSize*4);
          
            k1 = _k1;
            k2 = _k2;
            qm = _qm;
            ql = _ql;
            qr = _qr;
            qo = _qo;
            qc = _qc;
            domainPower = fft->log2(domainSize);
            internalWitness.resize(nAdditions);


            wFactor = fft->root(domainPower, 1);

            loadSigmas(_sigmas);

            loadFrElements(polQm, _QM, 0, domainSize);
            loadFrElements(polQl, _QL, 0, domainSize);
            loadFrElements(polQr, _QR, 0, domainSize);
            loadFrElements(polQo, _QO, 0, domainSize);
            loadFrElements(polQc, _QC, 0, domainSize);

            loadFrElements(polQm4, _QM, domainSize, domainSize * 4);
            loadFrElements(polQl4, _QL, domainSize, domainSize * 4);
            loadFrElements(polQr4, _QR, domainSize, domainSize * 4);
            loadFrElements(polQo4, _QO, domainSize, domainSize * 4);
            loadFrElements(polQc4, _QC, domainSize, domainSize * 4);
            loadFrElements(lPols, _lPols, 0, _lPolsSize/sizeof(FrElement));
        };

        ~Prover() {            
            delete fft;
        }

        std::unique_ptr<::Proof<Engine>> prove(FrElement *wtns);
        protected:
            void calculateAdditions (void);
            FrElement getWitness(u_int32_t index);
            void loadWitness(FrElement *wtns);
            void round1 ( void );
            void round2 ( void );
            void round3 ( void );
            void round4 ( void );
            void round5 ( void );
            void generateRandomBlindingScalars ( FrElements &randomBlindings );
            FrElements buildPolynomial ( FrElements &polynomial, FrElements &randomBlindings, std::vector<u_int32_t> randomBlindingIndexs );
            void evaluationsToCoefficients ( FrElements &polynomial );
            void coefficientsToEvaluations ( FrElements &polynomial );
            void setMontgomeryPolynomialFromWitnessMap ( FrElements &polynomial, u_int32_t *map );

            FrElements extendPolynomial ( const FrElements &polynomial, u_int32_t size );
            void polynomialToMontgomery ( FrElements &polynomial );
            void polynomialFromMontgomery ( FrElements &polynomial );
            typename Engine::G1Point expTau ( FrElements &polynomial );
            void calculateChallengeBeta ( void );
            void calculateChallengeGamma ( void );
            void calculateChallengeAlpha ( void );
            void calculateChallengeXi ( void );
            void calculateChallengeV ( void );
            void computePermutationPolynomialZ ( void );
            inline void computePermutationPolynomialZLoop ( int index, int n, FrElement &numerator, FrElement &denominator, const FrElement &betaW );
            void computeQuotientPolynomial ( void );
            FrElement evaluatePolynomial( const FrElements &pol, const FrElement &x );
            void loadFrElements ( FrElements &destination, const FrElement *source, u_int32_t offset, u_int32_t count, u_int32_t seek = 0 ); 
            void loadSigmas ( FrElement *sigmas );
            void calculateInverses ( FrElements &source );
            void multiplicateElements ( FrElements &destination, FrElements &a, FrElements &b );
            u_int64_t toRprBE(G1P &point, uint8_t *data, u_int64_t seek, u_int64_t size);
            void hashToFr(FrElement &element, u_int8_t *data, u_int64_t size);
            void settingZn ( void );
            inline void mul2 ( FrElement &r, FrElement &rz, const FrElement &a, const FrElement &b, const FrElement &ap, 
                               const FrElement &bp, int64_t p = -1 );
            inline void mul4 ( FrElement &r, FrElement &rz, const FrElement &a, const FrElement &b, const FrElement &c, 
                               const FrElement &d, const FrElement &ap, const FrElement &bp, const FrElement &cp, 
                               const FrElement &dp, int64_t p = -1 );
            inline FrElements div1 (const FrElements &pol, const FrElement &divisor);                                                                     
            void composeProof ( Proof<Engine> &proof );

    };
};

#include "plonk.cpp"
#endif