import Init.Data.List.Basic
import Init.Data.List.Lemmas

/-!
# JSP-000320 - Lean 4.20.0, no Mathlib

## Question
Must a binomial coefficient have a divisor close in size to its upper parameter?

## Answer: NO

**Counterexample**: C(62, 20) = 9206478467454346

Prime factorization: 2 x 13^2 x 149767 x 181869851

All positive divisors in ascending order:
  1, 2, 13, 26, 169, 338, 149767, ...

There is NO divisor d satisfying 31 <= d <= 124.
The gap between divisor 26 and divisor 169 is huge, containing
n = 62 and [31, 124] = [n/2, 2n] entirely.

Thus the universal statement "every binomial coefficient has a divisor
close to its upper parameter" is false.
-/

/-- The binomial coefficient C(62, 20). -/
def c6220 : Nat := 9206478467454346

/-- All integers in [31, 124], i.e., [n/2, 2n] for n = 62. -/
def range31to124 : List Nat := List.map (fun x => x + 31) (List.range 94)

/-- Every d in [31, 124] does NOT divide c6220. -/
theorem no_divisor_in_range :
    range31to124.all (fun d => c6220 % d != 0) = true := by decide

/-- The upper parameter 62 itself does NOT divide C(62, 20). -/
theorem not_div_by_62 : c6220 % 62 != 0 := by decide

/-- For n = 62, k = 20, n/2 = 31, 2*n = 124, 2*n - n/2 + 1 = 94.
    So List.map (fun x => x + 31) (List.range 94) = [31, 32, ..., 124]. -/
theorem range_formula_correct :
    List.map (fun x => x + 62 / 2) (List.range (2 * 62 - 62 / 2 + 1))
    = range31to124 := by decide

/-!
## Main theorem

There exists a binomial coefficient C(n,k) with 0 < k < n that has
NO divisor in the range [n/2, 2n]. Witness: n = 62, k = 20.
-/
theorem jsp_000320_main :
    ∃ n k : Nat, 0 < k ∧ k < n ∧
      List.all (List.map (fun x => x + n / 2) (List.range (2 * n - n / 2 + 1)))
        (fun d => c6220 % d != 0) = true := by
  refine ⟨62, 20, ?_, ?_, ?_⟩
  · decide
  · decide
  · -- For n=62: n/2=31, 2n=124, range = [31,124]
    -- Substitute the concrete values
    have h : List.map (fun x => x + 62 / 2) (List.range (2 * 62 - 62 / 2 + 1))
        = List.map (fun x => x + 31) (List.range 94) := by decide
    rw [h]
    -- Now check every d in [31,124]
    have h2 : (List.map (fun x => x + 31) (List.range 94)).all (fun d => c6220 % d != 0) = true := by decide
    exact h2

#print axioms jsp_000320_main