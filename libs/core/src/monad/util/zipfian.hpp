#pragma once

#include <monad/config.hpp>

#include <cmath>
#include <random>

MONAD_NAMESPACE_BEGIN

class ZipfDistribution
{
private:
    std::vector<double> cumulative_probs;

    double H(double const n, double const s)
    {
        double sum = 0.0;
        for (auto i = 1; i <= n; i++) {
            sum += 1.0 / std::pow(static_cast<double>(i), s);
        }
        return sum;
    }

public:
    ZipfDistribution(double const n, double const s)
    {
        auto harmonic_n = H(n, s);

        // precompute
        cumulative_probs.reserve(static_cast<size_t>(std::round(n)));
        double cumulative = 0.0;

        for (auto k = 1; k <= n; k++) {
            auto prob =
                1.0 / (std::pow(static_cast<double>(k), s) * harmonic_n);

            cumulative += prob;
            cumulative_probs.push_back(cumulative);
        }

        cumulative_probs.back() = 1.0;
    }

    template <typename RNG>
    int sample(RNG &rng)
    {
        std::uniform_real_distribution uniform(0.0, 1.0);
        double u = uniform(rng);

        // bin search bound
        auto it = std::lower_bound(
            cumulative_probs.begin(), cumulative_probs.end(), u);

        auto index = std::distance(cumulative_probs.begin(), it);
        return static_cast<int>(index);
    }
};

MONAD_NAMESPACE_END
