#ifndef __PROVER_H__
#define __PROVER_H__

#include "proof.hpp"

template <typename Engine>
class Prover {
public:
    virtual std::unique_ptr<Proof<Engine>> prove(typename Engine::FrElement *wtns) = 0;
};
#endif

