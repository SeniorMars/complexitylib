import NtimeDspace.ArithTerm
import NtimeDspace.HermiteTuple

/-!
# The Hermite weight as a term

The weight `∑_{d<J} c_d z^d` of `IntervalCoefficients.weightEvaluation`, with each
coefficient computed as a sum over digit tuples (`HermiteTuple`): the tuples are
the numbers `T < J ^ count`, with digits `T / J^i % J`.
-/

namespace NtimeDspace.ProgTerm

open Term

variable {w : List Bool}

/-- `x ^ e` exactly. -/
def powT (x e : Term) : Term := foldT e (const 1) fun acc _ => mul acc x

theorem powT_denote (x e : Term) (env : List ℕ) (hx : StableAt w x env) :
    (powT x e).denote w env = x.denote w env ^ e.denote w env := by
  simp only [powT, denote_foldT, denote_const]
  rw [foldAcc_eq _ env (fun acc _ => acc * x.denote w env) (fun acc k => by
    simp [hx.cons₂])]
  induction e.denote w env with
  | zero => rfl
  | succ m ih => rw [List.range_succ, List.foldl_append, ih]; simp [pow_succ]

theorem StableAt.powT {x e : Term} {env : List ℕ} (hx : StableAt w x env)
    (he : StableAt w e env) : StableAt w (powT x e) env := fun extra => by
  rw [powT_denote x e _ (hx.extend extra), powT_denote x e env hx, hx extra, he extra]

/-- The digit `T / x^i % x`. -/
def digitT (x T i : Term) : Term := mod (div T (powT x i)) x

theorem digitT_denote (x T i : Term) (env : List ℕ) (hx : StableAt w x env) :
    (digitT x T i).denote w env =
      T.denote w env / x.denote w env ^ i.denote w env % x.denote w env := by
  simp [digitT, powT_denote x i env hx]

theorem StableAt.digitT {x T i : Term} {env : List ℕ} (hx : StableAt w x env)
    (hT : StableAt w T env) (hi : StableAt w i env) : StableAt w (digitT x T i) env :=
  fun extra => by
    rw [digitT_denote x T i _ (hx.extend extra), digitT_denote x T i env hx, hx extra, hT extra,
      hi extra]

theorem finFunctionFinEquiv_symm_val {m n : ℕ} (T : Fin (m ^ n)) (i : Fin n) :
    ((finFunctionFinEquiv.symm T) i : ℕ) = T / m ^ (i : ℕ) % m := rfl

/-- A sum over the numbers below `m ^ n` is a sum over digit tuples. -/
theorem sum_range_pow_eq_tuples {M : Type*} [AddCommMonoid M] (m n : ℕ) (g : ℕ → M) :
    ∑ T ∈ Finset.range (m ^ n), g T = ∑ f : Fin n → Fin m, g (finFunctionFinEquiv f) := by
  rw [← Fin.sum_univ_eq_sum_range]
  exact (Equiv.sum_comp finFunctionFinEquiv (fun T : Fin (m ^ n) => g T)).symm

/-- The digit sum `∑_{i<count} T / x^i % x`. -/
def digitSumT (x count T : Term) : Term := sumT count fun i => digitT x T i

theorem digitSumT_denote (x count T : Term) (env : List ℕ) (hx : StableAt w x env)
    (hT : StableAt w T env) :
    (digitSumT x count T).denote w env = ∑ i ∈ Finset.range (count.denote w env),
      T.denote w env / x.denote w env ^ i % x.denote w env := by
  rw [digitSumT, denote_sumT _ _ env _ (fun acc i => by
    rw [digitT_denote x T _ _ (hx.extend₂ acc i), hx.cons₂, hT.cons₂, denote_lvl_index])]

theorem StableAt.digitSumT {x count T : Term} {env : List ℕ} (hx : StableAt w x env)
    (hc : StableAt w count env) (hT : StableAt w T env) :
    StableAt w (digitSumT x count T) env := fun extra => by
  rw [digitSumT_denote x count T _ (hx.extend extra) (hT.extend extra),
    digitSumT_denote x count T env hx hT, hx extra, hc extra, hT extra]

/-- The coefficient `[z^index] ∏_{i<count} (A i + z)^{-M i}` as a digit-tuple sum. -/
def coeffTupleT (p x count : Term) (A M : Term → Term) (index : Term) : Term :=
  Term.sumMod p (powT x count) fun T =>
    ite (eqT (digitSumT x count T) index)
      (Term.prodMod p count fun i => leafT p (A i) (M i) (digitT x T i)) (const 0)

theorem digit_finFunctionFinEquiv {m n : ℕ} (f : Fin n → Fin m) (i : Fin n) :
    (finFunctionFinEquiv f : ℕ) / m ^ (i : ℕ) % m = f i := by
  rw [← finFunctionFinEquiv_symm_val, Equiv.symm_apply_apply]

theorem coeffTupleT_denote {base : List ℕ} (p x count : Term) (A M : Term → Term)
    (index : Term) (extra : List ℕ) (P : ℕ) [Fact P.Prime] (hP : 2 < P)
    (Aspec Mspec : ℕ → ℕ) (hA : ImplementsFun w base A Aspec) (hM : ImplementsFun w base M Mspec)
    (hp : StableAt w p (extra ++ base)) (hpv : p.denote w (extra ++ base) = P)
    (hx : StableAt w x (extra ++ base)) (hc : StableAt w count (extra ++ base))
    (hidx : StableAt w index (extra ++ base)) :
    ((coeffTupleT p x count A M index).denote w (extra ++ base) : ZMod P) =
      ∑ f : Fin (count.denote w (extra ++ base)) → Fin (x.denote w (extra ++ base)),
        if ∑ i, (f i : ℕ) = index.denote w (extra ++ base) then
          ∏ i : Fin (count.denote w (extra ++ base)), HermiteRecovery.modularReciprocalCoefficient
            (Aspec (i : ℕ) : ZMod P) (Mspec (i : ℕ)) (f i)
        else 0 := by
  set env := extra ++ base with henv
  set X := x.denote w env
  set C := count.denote w env
  set I := index.denote w env
  let c : ℕ → ZMod P := fun T =>
    if ∑ i ∈ Finset.range C, T / X ^ i % X = I then
      ∏ i ∈ Finset.range C, HermiteRecovery.modularReciprocalCoefficient (Aspec i : ZMod P)
        (Mspec i) (T / X ^ i % X) else 0
  rw [coeffTupleT, denote_sumModZ p _ _ env P c hp hpv (fun acc T _ => ?_),
    powT_denote x count env hx, sum_range_pow_eq_tuples]
  · refine Finset.sum_congr rfl fun f _ => ?_
    have hsum : ∑ i ∈ Finset.range C, (finFunctionFinEquiv f : ℕ) / X ^ i % X =
        ∑ i, (f i : ℕ) := by
      rw [← Fin.sum_univ_eq_sum_range (fun i => (finFunctionFinEquiv f : ℕ) / X ^ i % X)]
      exact Finset.sum_congr rfl fun i _ => digit_finFunctionFinEquiv f i
    have hprod : ∏ i ∈ Finset.range C, HermiteRecovery.modularReciprocalCoefficient
        (Aspec i : ZMod P) (Mspec i) ((finFunctionFinEquiv f : ℕ) / X ^ i % X) =
        ∏ i : Fin C, HermiteRecovery.modularReciprocalCoefficient (Aspec (i : ℕ) : ZMod P)
          (Mspec (i : ℕ)) (f i) := by
      rw [← Fin.prod_univ_eq_prod_range (fun i => HermiteRecovery.modularReciprocalCoefficient
        (Aspec i : ZMod P) (Mspec i) ((finFunctionFinEquiv f : ℕ) / X ^ i % X))]
      exact Finset.prod_congr rfl fun i _ => by rw [digit_finFunctionFinEquiv f i]
    simp only [c, hsum, hprod]
    rfl
  · -- the body at a tuple `T`
    have hT := stableAt_index (w := w) env acc T
    have hsumv : (digitSumT x count (lvl env.length)).denote w (acc :: T :: env) =
        ∑ i ∈ Finset.range C, T / X ^ i % X := by
      rw [digitSumT_denote x count _ _ (hx.extend₂ acc T) hT, hx.cons₂, hc.cons₂,
        denote_lvl_index]
    simp only [denote_ite, denote_eqT, hsumv, hidx.cons₂, denote_const]
    by_cases hcond : ∑ i ∈ Finset.range C, T / X ^ i % X = I
    · rw [if_pos hcond, if_pos one_pos]
      simp only [c, if_pos hcond]
      rw [denote_prodModZ p count _ (acc :: T :: env) P (fun i =>
          HermiteRecovery.modularReciprocalCoefficient (Aspec i : ZMod P) (Mspec i)
            (T / X ^ i % X)) (hp.extend₂ acc T) (by rw [hp.cons₂]; exact hpv)
          (fun acc' i _ => ?_), hc.cons₂]
      have hi := stableAt_index (w := w) (acc :: T :: env) acc' i
      have hAi := hA (acc' :: i :: acc :: T :: extra) (lvl (acc :: T :: env).length)
        (by simpa [env] using hi)
      have hMi := hM (acc' :: i :: acc :: T :: extra) (lvl (acc :: T :: env).length)
        (by simpa [env] using hi)
      simp only [List.cons_append, ← henv, denote_lvl_index] at hAi hMi
      rw [leafT_denote p _ _ _ _ P hP ((hp.extend₂ acc T).extend₂ acc' i)
        (by rw [show acc' :: i :: acc :: T :: env = [acc', i, acc, T] ++ env from rfl, hp]
            exact hpv) hAi.2 hMi.2, hAi.1, hMi.1,
        digitT_denote x _ _ _ ((hx.extend₂ acc T).extend₂ acc' i),
        show acc' :: i :: acc :: T :: env = [acc', i, acc, T] ++ env from rfl, hx]
      simp [Term.denote_lvl, Nat.add_assoc, Nat.add_sub_cancel_left, Nat.add_sub_add_left]
      rfl
    · rw [if_neg hcond, if_neg (lt_irrefl 0)]
      simp [c, hcond]

/-- The Hermite weight `∑_{d<x} c_d z^d` modulo `p`. -/
def weightT (p x count : Term) (A M : Term → Term) (z : Term) : Term :=
  Term.sumMod p x fun idx => mod (mul (coeffTupleT p x count A M idx) (powModT p z idx)) p

/-- **The weight term computes `IntervalCoefficients.weightEvaluation`.** -/
theorem weightT_denote {base : List ℕ} (p x count : Term) (A M : Term → Term) (z : Term)
    (extra : List ℕ) (P : ℕ) [Fact P.Prime] (hP : 2 < P)
    (Aspec Mspec : ℕ → ℕ) (hA : ImplementsFun w base A Aspec) (hM : ImplementsFun w base M Mspec)
    (hp : StableAt w p (extra ++ base)) (hpv : p.denote w (extra ++ base) = P)
    (hx : StableAt w x (extra ++ base)) (hc : StableAt w count (extra ++ base))
    (hz : StableAt w z (extra ++ base))
    (hxP : x.denote w (extra ++ base) ≤ P)
    (valid : IntervalCoefficients.Valid (fun i => ((Aspec i : ZMod P), Mspec i))
      (count.denote w (extra ++ base))) :
    ((weightT p x count A M z).denote w (extra ++ base) : ZMod P) =
      IntervalCoefficients.weightEvaluation (fun i => ((Aspec i : ZMod P), Mspec i))
        (count.denote w (extra ++ base)) (x.denote w (extra ++ base))
        (z.denote w (extra ++ base) : ZMod P) := by
  set env := extra ++ base with henv
  set factor : IntervalCoefficients.Factors P := fun i => ((Aspec i : ZMod P), Mspec i)
  rw [weightT, denote_sumModZ p x _ env P (fun idx =>
      IntervalCoefficients.allCoefficient factor (count.denote w env) idx *
        (z.denote w env : ZMod P) ^ idx) hp hpv (fun acc idx hlt => ?_),
    IntervalCoefficients.weightEvaluation, sumLoop_correct, add_zero]
  have hidx : StableAt w (lvl env.length) ((acc :: idx :: extra) ++ base) :=
    stableAt_index env acc idx
  have hcoef := coeffTupleT_denote p x count A M (lvl env.length) (acc :: idx :: extra) P hP
    Aspec Mspec hA hM (hp.extend₂ acc idx) (by
      show p.denote w (acc :: idx :: env) = P; rw [hp.cons₂]; exact hpv)
    (hx.extend₂ acc idx) (hc.extend₂ acc idx) hidx
  simp only [List.cons_append, ← henv] at hcoef
  rw [denote_lvl_index] at hcoef
  have hX : x.denote w (acc :: idx :: env) = x.denote w env := hx.cons₂ acc idx
  have key := HermiteTuple.allCoefficient_eq_tuple factor (count.denote w (acc :: idx :: env))
    (by rw [hc.cons₂]; exact valid) (x.denote w (acc :: idx :: env)) idx
    (by rw [hX]; exact hlt) (by rw [hX]; exact hxP)
  simp only [factor] at key
  simp only [denote_mod, denote_mul, ZMod.natCast_mod, Nat.cast_mul, hp.cons₂, hpv]
  rw [hcoef, ← key, hc.cons₂, powModT_denote p z (lvl env.length) (acc :: idx :: env) P
    (hp.extend₂ acc idx) (by rw [hp.cons₂]; exact hpv) (hz.extend₂ acc idx), hz.cons₂,
    denote_lvl_index]

end NtimeDspace.ProgTerm
