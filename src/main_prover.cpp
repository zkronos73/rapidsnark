#include <sys/mman.h>
#include <sys/stat.h>
#include <fcntl.h>
#include <unistd.h>
#include <iostream>
#include <fstream>
#include <gmp.h>
#include <memory>
#include <stdexcept>
#include <nlohmann/json.hpp>

#include <alt_bn128.hpp>
#include "binfile_utils.hpp"
#include "zkey_utils.hpp"
#include "wtns_utils.hpp"
#include "groth16.hpp"
#include "plonk.hpp"

using json = nlohmann::json;

#define handle_error(msg) \
           do { perror(msg); exit(EXIT_FAILURE); } while (0)

int main(int argc, char **argv) {

    if (argc != 5) {
        std::cerr << "Invalid number of parameters:\n";
        std::cerr << "Usage: prove <circuit.zkey> <witness.wtns> <proof.json> <public.json>\n";
        return -1;
    }

    mpz_t altBbn128r;

    mpz_init(altBbn128r);
    mpz_set_str(altBbn128r, "21888242871839275222246405745257275088548364400416034343698204186575808495617", 10);

    try {
        std::string zkeyFilename = argv[1];
        std::string wtnsFilename = argv[2];
        std::string proofFilename = argv[3];
        std::string publicFilename = argv[4];

        auto zkey = BinFileUtils::openExisting(zkeyFilename, "zkey", 1);
        auto zkeyHeader = ZKeyUtils::loadHeader(zkey.get());

        std::string proofStr;
        if (mpz_cmp(zkeyHeader->rPrime, altBbn128r) != 0) {
            throw std::invalid_argument( "zkey curve not supported" );
        }
        
        auto wtns = BinFileUtils::openExisting(wtnsFilename, "wtns", 2);
        auto wtnsHeader = WtnsUtils::loadHeader(wtns.get());
        
        if (mpz_cmp(wtnsHeader->prime, altBbn128r) != 0) {
            throw std::invalid_argument( "different wtns curve" );
        }

    std::unique_ptr<Prover<AltBn128::Engine>, std::default_delete<Prover<AltBn128::Engine> > > prover;

    if (zkeyHeader->protocol == 1) {
        prover = Groth16::makeProver<AltBn128::Engine>(
            zkeyHeader->nVars,
            zkeyHeader->nPublic,
            zkeyHeader->domainSize,
            zkeyHeader->nCoefs,
            zkeyHeader->vk_alpha1,
            zkeyHeader->vk_beta1,
            zkeyHeader->vk_beta2,
            zkeyHeader->vk_delta1,
            zkeyHeader->vk_delta2,
            zkey->getSectionData(4),    // Coefs
            zkey->getSectionData(5),    // pointsA
            zkey->getSectionData(6),    // pointsB1
            zkey->getSectionData(7),    // pointsB2
            zkey->getSectionData(8),    // pointsC
            zkey->getSectionData(9)     // pointsH1
        );
    }
    else {
        prover = Plonk::makeProver<AltBn128::Engine>(
            zkeyHeader->nVars,
            zkeyHeader->nPublic,
            zkeyHeader->domainSize,
            zkeyHeader->nConstrains,
            zkeyHeader->nAdditions,
            zkey->getSectionSize(13),
            zkey->getSectionSize(14),
            zkeyHeader->k1,
            zkeyHeader->k2,
            zkeyHeader->qm,
            zkeyHeader->ql,
            zkeyHeader->qr,
            zkeyHeader->qo,
            zkeyHeader->qc,
            zkey->getSectionData(3),    // Additions
            zkey->getSectionData(4),    // aMap
            zkey->getSectionData(5),    // bMap
            zkey->getSectionData(6),    // cMap
            zkey->getSectionData(7),    // QM4
            zkey->getSectionData(8),    // QL4
            zkey->getSectionData(9),    // QR4
            zkey->getSectionData(10),   // QO4
            zkey->getSectionData(11),   // QC4
            zkey->getSectionData(13),   // lpols
            zkey->getSectionData(14),   // Tau
            zkey->getSectionData(12)    // Sigma1, Sigma2, Sigma3 (pol, pol-ext)
        );
    }

        AltBn128::FrElement *wtnsData = (AltBn128::FrElement *)wtns->getSectionData(2);
        auto proof = prover->prove(wtnsData);

        std::ofstream proofFile;
        proofFile.open (proofFilename);
        proofFile << proof->toJson();
        proofFile.close();

        std::ofstream publicFile;
        publicFile.open (publicFilename);

        json jsonPublic;
        AltBn128::FrElement aux;
        for (int i=1; i<=zkeyHeader->nPublic; i++) {
            AltBn128::Fr.toMontgomery(aux, wtnsData[i]);
            jsonPublic.push_back(AltBn128::Fr.toString(aux));
        }

        publicFile << jsonPublic;
        publicFile.close();

    } catch (std::exception& e) {
        mpz_clear(altBbn128r);
        std::cerr << e.what() << '\n';
        return -1;
    }

    mpz_clear(altBbn128r);
    exit(EXIT_SUCCESS);
}
