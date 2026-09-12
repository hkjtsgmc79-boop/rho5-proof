#pragma once
#include "mc_exact_model.hpp"
constexpr int NV=EV,NX=EN;
const auto &pairs=epairs;
inline const std::vector<std::vector<double>> base=[](){std::vector<std::vector<double>> a;for(auto&r:ebase)a.emplace_back(r.begin(),r.end());return a;}();
inline const std::vector<double> rhs(erhs.begin(),erhs.end());
