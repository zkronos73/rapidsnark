#ifndef __PROOF_H__
#define __PROOF_H__

template <typename Engine>
class Proof {
public:
    virtual std::string toJsonStr() = 0;
    virtual json toJson() = 0;
};

#endif