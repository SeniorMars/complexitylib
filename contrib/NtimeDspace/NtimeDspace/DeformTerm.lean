import NtimeDspace.LabelTerm
import NtimeDspace.DeformationEvaluation

/-!
# Parity interpolation and the deformation entries as terms

The signed window start is held as two naturals, `start = sP - sN`. Terms for
the parity interpolant (`ParityEvaluation.evaluate`), the bad-label test, the
spectral coefficient `beta`, the residual over bad labels, and the matrix
`entry` and `coefficient` of `DeformationEvaluation`, all modulo `p`.
-/

namespace NtimeDspace.ProgTerm

open Term

variable {w : List Bool}

/-- `a - b` modulo `p`. -/
def subModT (pT a b : Term) : Term := mod (add a (sub pT (mod b pT))) pT

theorem cast_subModT {P : ℕ} (hP : 0 < P) (pT a b : Term) (env : List ℕ)
    (hpv : pT.denote w env = P) :
    ((subModT pT a b).denote w env : ZMod P) = (a.denote w env : ZMod P) - b.denote w env := by
  simp only [subModT, denote_mod, denote_add, denote_sub, hpv]
  exact cast_mod_add_sub_mod P _ _ hP

theorem StableAt.subModT {pT a b : Term} {env : List ℕ} (hp : StableAt w pT env)
    (ha : StableAt w a env) (hb : StableAt w b env) : StableAt w (subModT pT a b) env :=
  (ha.add (hp.sub (hb.mod hp))).mod hp

/-- The residue of `start + j`, for `start = sP - sN`. -/
def nodeT (pT sP sN j : Term) : Term := subModT pT (add sP j) sN

theorem cast_nodeT {P : ℕ} [Fact P.Prime] (hP : 0 < P) (pT sP sN j : Term) (env : List ℕ)
    (hpv : pT.denote w env = P) :
    ((nodeT pT sP sN j).denote w env : ZMod P) =
      ParityEvaluation.node P ((sP.denote w env : ℤ) - sN.denote w env) (j.denote w env) := by
  rw [nodeT, cast_subModT hP _ _ _ env hpv, denote_add]
  unfold ParityEvaluation.node
  push_cast
  ring

/-- A Lagrange basis value on the window. -/
def basisT (pT sP sN width slot x : Term) : Term :=
  Term.prodMod pT width fun other => ite (eqT other slot) (const 1)
    (mod (mul (subModT pT x (nodeT pT sP sN other))
      (invModT pT (subModT pT (nodeT pT sP sN slot) (nodeT pT sP sN other)))) pT)

/-- The parity interpolant at `x`. -/
def parityT (pT sP sN width x : Term) : Term :=
  Term.sumMod pT width fun slot =>
    mod (mul (signT pT (add (add sP slot) sN)) (basisT pT sP sN width slot x)) pT

theorem StableAt.nodeT {pT sP sN j : Term} {env : List ℕ} (hp : StableAt w pT env)
    (h1 : StableAt w sP env) (h2 : StableAt w sN env) (hj : StableAt w j env) :
    StableAt w (nodeT pT sP sN j) env := StableAt.subModT hp (h1.add hj) h2

section Parity

variable {P : ℕ} [Fact P.Prime] {pT sP sN widthT : Term} {env : List ℕ}

theorem cast_basisT (hP3 : 2 < P) (hp : StableAt w pT env) (hpv : pT.denote w env = P)
    (hsP : StableAt w sP env) (hsN : StableAt w sN env) {slot x : Term}
    (hslot : StableAt w slot env) (hx : StableAt w x env) :
    ((basisT pT sP sN widthT slot x).denote w env : ZMod P) =
      ParityEvaluation.basisValue P ((sP.denote w env : ℤ) - sN.denote w env) (widthT.denote w env)
        (slot.denote w env) (x.denote w env : ZMod P) := by
  have hP0 : 0 < P := by omega
  unfold basisT ParityEvaluation.basisValue
  rw [ParityEvaluation.productLoop_correct, mul_one,
    denote_prodModZ pT widthT _ env P (fun other => if other = slot.denote w env then 1 else
      ((x.denote w env : ZMod P) - ParityEvaluation.node P ((sP.denote w env : ℤ) - sN.denote w env)
        other) / (ParityEvaluation.node P ((sP.denote w env : ℤ) - sN.denote w env) (slot.denote w env) -
        ParityEvaluation.node P ((sP.denote w env : ℤ) - sN.denote w env) other)) hp hpv]
  intro acc other _
  set env' := acc :: other :: env
  have e' : env' = [acc, other] ++ env := rfl
  have hp' : StableAt w pT env' := hp.extend [acc, other]
  have hpv' : pT.denote w env' = P := by rw [hp.cons₂, hpv]
  have hov : (lvl env.length).denote w env' = other := denote_lvl_index env acc other
  have hos : StableAt w (lvl env.length) env' := stableAt_lvl (by simp [env'])
  rw [denote_ite, denote_eqT, hov, hslot.cons₂]
  by_cases h : other = slot.denote w env
  · simp [h]
  · rw [if_neg h, if_neg (lt_irrefl 0), denote_mod, hpv', ZMod.natCast_mod, denote_mul,
      Nat.cast_mul, cast_subModT hP0 _ _ _ env' hpv',
      invModT_denote pT _ env' P hP3 hp' hpv'
        (StableAt.subModT hp' (StableAt.nodeT hp' (hsP.extend [acc, other])
          (hsN.extend [acc, other]) (hslot.extend [acc, other]))
          (StableAt.nodeT hp' (hsP.extend [acc, other]) (hsN.extend [acc, other]) hos)),
      cast_subModT hP0 _ _ _ env' hpv']
    have e1 : x.denote w env' = x.denote w env := hx.cons₂ acc other
    have e2 : sP.denote w env' = sP.denote w env := hsP.cons₂ acc other
    have e3 : sN.denote w env' = sN.denote w env := hsN.cons₂ acc other
    have e4 : slot.denote w env' = slot.denote w env := hslot.cons₂ acc other
    simp only [cast_nodeT hP0 _ _ _ _ env' hpv', e1, e2, e3, e4, hov, div_eq_mul_inv, if_neg h]

theorem paritySign_sub (a b c : ℕ) :
    ParityEvaluation.paritySign P ((a : ℤ) - b + c) = (-1 : ZMod P) ^ (a + c + b) := by
  unfold ParityEvaluation.paritySign
  rcases Nat.even_or_odd (a + c + b) with h | h
  · rw [h.neg_one_pow, if_pos]
    obtain ⟨m, hm⟩ := h
    omega
  · rw [h.neg_one_pow, if_neg]
    obtain ⟨m, hm⟩ := h
    omega

theorem cast_parityT (hP3 : 2 < P) (hp : StableAt w pT env) (hpv : pT.denote w env = P)
    (hsP : StableAt w sP env) (hsN : StableAt w sN env) (hwd : StableAt w widthT env)
    {x : Term} (hx : StableAt w x env) :
    ((parityT pT sP sN widthT x).denote w env : ZMod P) =
      ParityEvaluation.evaluate P ((sP.denote w env : ℤ) - sN.denote w env) (widthT.denote w env)
        (x.denote w env : ZMod P) := by
  unfold parityT ParityEvaluation.evaluate
  rw [sumLoop_correct, add_zero,
    denote_sumModZ pT widthT _ env P (fun slot =>
      ParityEvaluation.paritySign P ((sP.denote w env : ℤ) - sN.denote w env + slot) *
        ParityEvaluation.basisValue P ((sP.denote w env : ℤ) - sN.denote w env)
          (widthT.denote w env) slot (x.denote w env : ZMod P)) hp hpv]
  intro acc slot _
  set env' := acc :: slot :: env
  have hp' : StableAt w pT env' := hp.extend [acc, slot]
  have hpv' : pT.denote w env' = P := by rw [hp.cons₂, hpv]
  have hsv : (lvl env.length).denote w env' = slot := denote_lvl_index env acc slot
  have hss : StableAt w (lvl env.length) env' := stableAt_lvl (by simp [env'])
  rw [denote_mod, hpv', ZMod.natCast_mod, denote_mul, Nat.cast_mul,
    signT_denote pT _ env' P (by omega) hpv',
    cast_basisT hP3 hp' hpv' (hsP.extend [acc, slot]) (hsN.extend [acc, slot]) hss
      (hx.extend [acc, slot]), paritySign_sub]
  have e1 : x.denote w env' = x.denote w env := hx.cons₂ acc slot
  have e2 : sP.denote w env' = sP.denote w env := hsP.cons₂ acc slot
  have e3 : sN.denote w env' = sN.denote w env := hsN.cons₂ acc slot
  have e4 : widthT.denote w env' = widthT.denote w env := hwd.cons₂ acc slot
  simp only [denote_add, e1, e2, e3, e4, hsv]

end Parity

end NtimeDspace.ProgTerm
