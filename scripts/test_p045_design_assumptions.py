"""Exact finite-design witnesses for the independence assumptions in P045.

These tests enumerate randomization laws independently of the Lean implementation.
They demonstrate why uniform marginal assignments alone do not imply the stated
selected-mean or variance formulas.
"""
from fractions import Fraction
from itertools import combinations, product
import unittest


def mean(values):
    return sum(values, Fraction(0)) / len(values)


def variance(values):
    average = mean(values)
    return mean([(value - average) ** 2 for value in values])


class DesignAssumptionsTest(unittest.TestCase):
    def test_selected_mean_requires_independence_from_selection(self):
        # Two one-unit groups; select one uniformly and use treatment as X_g.
        # If the selected group is treated, each marginal remains Bernoulli(1/2).
        dependent = [(g, tuple(int(j == g) for j in range(2))) for g in range(2)]
        self.assertEqual([mean([z[g] for _, z in dependent]) for g in range(2)],
                         [Fraction(1, 2), Fraction(1, 2)])
        self.assertEqual(mean([z[g] for g, z in dependent]), 1)
        # Under the product law, selection and both Bernoulli assignments vary
        # independently, restoring the average of the marginal expectations.
        independent = list(product(range(2), product(range(2), repeat=2)))
        self.assertEqual(mean([z[g] for g, z in independent]), Fraction(1, 2))

    def test_direct_variance_requires_independent_group_assignments(self):
        # Both four-unit groups have y(0)=y(1)=(0,0,1,1); treat two in each.
        outcomes = (0, 0, 1, 1)
        treated_pairs = list(combinations(range(4), 2))

        def contrast(pair):
            treated = mean([outcomes[i] for i in pair])
            control = mean([outcomes[i] for i in range(4) if i not in pair])
            return treated - control

        group_estimates = [contrast(pair) for pair in treated_pairs]
        shared_assignments = [mean([contrast(pair), contrast(pair)]) for pair in treated_pairs]
        independent_assignments = [mean([contrast(a), contrast(b)])
                                   for a, b in product(treated_pairs, repeat=2)]
        self.assertEqual(mean(group_estimates), 0)
        self.assertEqual(variance(group_estimates), Fraction(1, 3))
        self.assertEqual(variance(shared_assignments), Fraction(1, 3))
        self.assertEqual(variance(independent_assignments), Fraction(1, 6))
        # G=C=2 and zero group effects make the displayed variance formula
        # (V_1+V_2)/(C*G), equal to the product-law variance.
        displayed = (variance(group_estimates) + variance(group_estimates)) / (2 * 2)
        self.assertEqual(displayed, variance(independent_assignments))
        self.assertNotEqual(displayed, variance(shared_assignments))


if __name__ == '__main__':
    unittest.main()
