#include <stdexcept>

#include "zkey_utils.hpp"

namespace ZKeyUtils {


Header::Header() {
}

Header::~Header() {
    mpz_clear(qPrime);
    mpz_clear(rPrime);
}

std::unique_ptr<Header> readHeaderGroth16(BinFileUtils::BinFile *f);
std::unique_ptr<Header> readHeaderPlonk(BinFileUtils::BinFile *f);

std::unique_ptr<Header> loadHeader(BinFileUtils::BinFile *f) {

    f->startReadSection(1);
    uint32_t protocol = f->readU32LE();
    f->endReadSection();

    // TODO: protocol as define
    if (protocol == 1) {
        return readHeaderGroth16(f);
    }
    else if (protocol == 2) {
        return readHeaderPlonk(f);
    }
    else {
        throw std::invalid_argument( "protocol of zkey file is not reconozied" );
    }
}

std::unique_ptr<Header> readHeaderGroth16(BinFileUtils::BinFile *f) {
    auto h = new Header();

    h->protocol = 1;
    f->startReadSection(2);


    h->n8q = f->readU32LE();
    mpz_init(h->qPrime);
    mpz_import(h->qPrime, h->n8q, -1, 1, -1, 0, f->read(h->n8q));

    h->n8r = f->readU32LE();
    mpz_init(h->rPrime);
    mpz_import(h->rPrime, h->n8r , -1, 1, -1, 0, f->read(h->n8r));

    h->nVars = f->readU32LE();
    h->nPublic = f->readU32LE();
    h->domainSize = f->readU32LE();

    h->vk_alpha1 = f->read(h->n8q*2);
    h->vk_beta1 = f->read(h->n8q*2);
    h->vk_beta2 = f->read(h->n8q*4);
    h->vk_gamma2 = f->read(h->n8q*4);
    h->vk_delta1 = f->read(h->n8q*2);
    h->vk_delta2 = f->read(h->n8q*4);
    f->endReadSection();

    h->nCoefs = f->getSectionSize(4) / (12 + h->n8r);

    return std::unique_ptr<Header>(h);
}

std::unique_ptr<Header> readHeaderPlonk(BinFileUtils::BinFile *f) {
    auto h = new Header();

    h->protocol = 2;
    f->startReadSection(2);

    h->n8q = f->readU32LE();
    mpz_init(h->qPrime);
    mpz_import(h->qPrime, h->n8q, -1, 1, -1, 0, f->read(h->n8q));

    h->n8r = f->readU32LE();
    mpz_init(h->rPrime);
    mpz_import(h->rPrime, h->n8r , -1, 1, -1, 0, f->read(h->n8r));

    h->nVars = f->readU32LE();
    h->nPublic = f->readU32LE();
    h->domainSize = f->readU32LE();

    h->nAdditions = f->readU32LE();
    h->nConstrains = f->readU32LE();
    h->k1 = f->read(h->n8r);
    h->k2 = f->read(h->n8r);

    h->qm = f->read(h->n8q*2);
    h->qr = f->read(h->n8q*2);
    h->ql = f->read(h->n8q*2);
    h->qo = f->read(h->n8q*2);
    h->qc = f->read(h->n8q*2);
    h->s1 = f->read(h->n8q*2);
    h->s2 = f->read(h->n8q*2);
    h->s3 = f->read(h->n8q*2);
    h->x2 = f->read(h->n8q*4);

    f->endReadSection();
    
    return std::unique_ptr<Header>(h);
}


} // namespace

