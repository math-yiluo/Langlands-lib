/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.Adic.IntegralLatticeLocal
public import WeilConjectures.SixFunctors.ProEtale.Adic.ZModPowCokernel

/-!
# The tower `(ℤ/ℓⁿ)_X` is `ℓ`-adic

Restricted to any object `Y` of `X_proét`, the transition `(ℤ/ℓⁿ⁺¹)_X ⟶ (ℤ/ℓⁿ)_X` of the tower
of abelian sheaves `n ↦ (ℤ/ℓⁿ)_X` is a cokernel of multiplication by `ℓⁿ`
(`AlgebraicGeometry.ProEtale.exists_isColimit_cokernelCofork_zmodPowAbSheafDiagram`): on
sections, reduction `C(U, ℤ/ℓⁿ⁺¹) ⟶ C(U, ℤ/ℓⁿ)` of locally constant functions is surjective
with kernel `ℓⁿ C(U, ℤ/ℓⁿ⁺¹)`, the values being lifted pointwise, which preserves continuity
as `ℤ/ℓⁿ⁺¹` is discrete.

Hence `lim Gₙ` is locally `ℤ_ℓ,X` for an `ℓ`-adic tower `(Gₙ)` of sheaves locally isomorphic to
`(ℤ/ℓⁿ)_X`, as soon as automorphisms of `(ℤ/ℓⁿ)_X` lift locally to `(ℤ/ℓⁿ⁺¹)_X`
(`AlgebraicGeometry.ProEtale.exists_cover_nonempty_iso_padicIntAbSheaf_of_lift_aut`).
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite

namespace ZMod

/-- An element of `ℤ/n` which vanishes in `ℤ/m`, for `m ∣ n`, is a multiple of `m`. -/
lemma exists_mul_eq_of_castHom_eq_zero {m n : ℕ} [NeZero n] (h : m ∣ n) {z : ZMod n}
    (hz : castHom h (ZMod m) z = 0) : ∃ y : ZMod n, (m : ZMod n) * y = z := by
  rw [castHom_apply, cast_eq_val, natCast_eq_zero_iff] at hz
  obtain ⟨q, hq⟩ := hz
  exact ⟨q, by rw [← Nat.cast_mul, ← hq, natCast_zmod_val]⟩

end ZMod

namespace AlgebraicGeometry.ProEtale

open Scheme

variable (X : Scheme.{u}) (l : ℕ) [Fact l.Prime]

/-- **The tower `(ℤ/ℓⁿ)_X` is `ℓ`-adic**: restricted to any `Y`, the transition
`(ℤ/ℓⁿ⁺¹)_X ⟶ (ℤ/ℓⁿ)_X` is a cokernel of multiplication by `ℓⁿ`. -/
theorem exists_isColimit_cokernelCofork_zmodPowAbSheafDiagram (n : ℕ) (Y : X.ProEt) :
    ∃ w : (((l ^ n : ℕ) : ℤ) • 𝟙 _) ≫ ((ProEt.topology X).overPullback Ab.{u + 1} Y).map
        ((zmodPowAbSheafDiagram X l).map (homOfLE n.le_succ).op) = 0,
      Nonempty (IsColimit (CokernelCofork.ofπ _ w)) := by
  have hdvd : l ^ n ∣ l ^ (n + 1) := pow_dvd_pow l n.le_succ
  let c : C(ZMod (l ^ (n + 1)), ZMod (l ^ n)) :=
    ⟨ZMod.castHom hdvd _, continuous_of_discreteTopology⟩
  let π := ((ProEt.topology X).overPullback Ab.{u + 1} Y).map
    ((zmodPowAbSheafDiagram X l).map (homOfLE n.le_succ).op)
  have hπ (U : (Over Y)ᵒᵖ) (x : (((ProEt.topology X).overPullback Ab.{u + 1} Y).obj
      ((zmodPowAbSheafDiagram X l).obj (op (n + 1)))).obj.obj U) :
      π.hom.app U x = ULift.up (c.comp x.down) := rfl
  have hN (U : (Over Y)ᵒᵖ) (x : (((ProEt.topology X).overPullback Ab.{u + 1} Y).obj
      ((zmodPowAbSheafDiagram X l).obj (op (n + 1)))).obj.obj U) :
      ((((l ^ n : ℕ) : ℤ) • 𝟙 (((ProEt.topology X).overPullback Ab.{u + 1} Y).obj
        ((zmodPowAbSheafDiagram X l).obj (op (n + 1))))).hom.app U) x =
        ((l ^ n : ℕ) : ℤ) • x := rfl
  have w : (((l ^ n : ℕ) : ℤ) • 𝟙 _) ≫ π = 0 := by
    refine ObjectProperty.hom_ext _ (NatTrans.ext (funext fun U ↦ ?_))
    ext x
    refine ULift.ext (ContinuousMap.ext fun t ↦ ?_)
    have h : (((((l ^ n : ℕ) : ℤ) • 𝟙 _) ≫ π).hom.app U x) =
        π.hom.app U (((l ^ n : ℕ) : ℤ) • x) := rfl
    rw [h, hπ]
    refine (map_zsmul (ZMod.castHom hdvd (ZMod (l ^ n))) _ (x.down t)).trans ?_
    rw [zsmul_eq_mul, Int.cast_natCast, ZMod.natCast_self, zero_mul]
    rfl
  have : NeZero l := ⟨(Fact.out : l.Prime).ne_zero⟩
  refine ⟨w, ⟨Sheaf.isColimitCokernelCoforkOfSurjective _ π w (fun U x ↦ ?_)
    (fun U x hx ↦ ?_)⟩⟩
  · let s := Function.surjInv (ZMod.castHom_surjective hdvd)
    refine ⟨ULift.up ((⟨s, continuous_of_discreteTopology⟩ :
      C(ZMod (l ^ n), ZMod (l ^ (n + 1)))).comp x.down), ?_⟩
    rw [hπ]
    exact ULift.ext (ContinuousMap.ext fun t ↦
      Function.surjInv_eq (ZMod.castHom_surjective hdvd) _)
  · have ht (t : _) : ZMod.castHom hdvd (ZMod (l ^ n)) (x.down t) = 0 :=
      congrArg (fun y : ULift.{u + 1} C(_, ZMod (l ^ n)) ↦ y.down t) ((hπ U x).symm.trans hx)
    let d : ZMod (l ^ (n + 1)) → ZMod (l ^ (n + 1)) := fun z ↦
      if hz : ZMod.castHom hdvd (ZMod (l ^ n)) z = 0 then
        (ZMod.exists_mul_eq_of_castHom_eq_zero hdvd hz).choose else 0
    refine ⟨ULift.up ((⟨d, continuous_of_discreteTopology⟩ :
      C(ZMod (l ^ (n + 1)), ZMod (l ^ (n + 1)))).comp x.down), ?_⟩
    rw [hN]
    refine ULift.ext (ContinuousMap.ext fun t ↦ ?_)
    have hd : (((l ^ n : ℕ) : ℤ) • (ULift.up ((⟨d, continuous_of_discreteTopology⟩ :
        C(ZMod (l ^ (n + 1)), ZMod (l ^ (n + 1)))).comp x.down) :
          (((ProEt.topology X).overPullback Ab.{u + 1} Y).obj
            ((zmodPowAbSheafDiagram X l).obj (op (n + 1)))).obj.obj U)).down t =
        ((l ^ n : ℕ) : ℤ) • d (x.down t) := rfl
    rw [hd, zsmul_eq_mul, Int.cast_natCast]
    simp only [d, dite_eq_left (ht t)]
    exact (ZMod.exists_mul_eq_of_castHom_eq_zero hdvd (ht t)).choose_spec

/-- **An `ℓ`-adic tower of locally constant sheaves of rank one has a lattice which is locally
`ℤ_ℓ,X`**, given local lifting of automorphisms of the constant tower `(ℤ/ℓⁿ)_X` (`haut`): the
cokernel property of the constant tower is
`AlgebraicGeometry.ProEtale.exists_isColimit_cokernelCofork_zmodPowAbSheafDiagram`. -/
theorem exists_cover_nonempty_iso_padicIntAbSheaf_of_lift_aut
    (G : ℕᵒᵖ ⥤ Sheaf (ProEt.topology X) Ab.{u + 1})
    (hG : ∀ (n : ℕ) (Y : X.ProEt), ∃ w : (((l ^ n : ℕ) : ℤ) • 𝟙 _) ≫
        ((ProEt.topology X).overPullback Ab.{u + 1} Y).map (G.map (homOfLE n.le_succ).op) = 0,
      Nonempty (IsColimit (CokernelCofork.ofπ _ w)))
    (hloc : ∀ (n : ℕ) (V : X.ProEt), ∃ S ∈ ProEt.topology X V,
      ∀ ⦃Y : X.ProEt⦄ (f : Y ⟶ V), S f →
        Nonempty ((isoPresheaf ((zmodPowAbSheafDiagram X l).obj (op n)) (G.obj (op n))).obj
          (op Y)))
    (haut : ∀ (n : ℕ) (Y : X.ProEt) (α : (isoPresheaf ((zmodPowAbSheafDiagram X l).obj (op n))
        ((zmodPowAbSheafDiagram X l).obj (op n))).obj (op Y)),
      ∃ S ∈ ProEt.topology X Y, ∀ ⦃Z : X.ProEt⦄ (h : Z ⟶ Y), S h →
        ∃ β : (isoPresheaf ((zmodPowAbSheafDiagram X l).obj (op (n + 1)))
            ((zmodPowAbSheafDiagram X l).obj (op (n + 1)))).obj (op Z),
          β.hom ≫ ((ProEt.topology X).overPullback Ab.{u + 1} Z).map
              ((zmodPowAbSheafDiagram X l).map (homOfLE n.le_succ).op) =
            ((ProEt.topology X).overPullback Ab.{u + 1} Z).map
                ((zmodPowAbSheafDiagram X l).map (homOfLE n.le_succ).op) ≫
              ((isoPresheaf _ _).map h.op α).hom)
    (V : X.ProEt) :
    ∃ (ι : Type u) (W : ι → X.ProEt) (f : ∀ i, W i ⟶ V),
      Sieve.ofArrows W f ∈ ProEt.topology X V ∧
      ∀ i, Nonempty (((ProEt.topology X).overPullback Ab.{u + 1} (W i)).obj (limit G) ≅
        ((ProEt.topology X).overPullback Ab.{u + 1} (W i)).obj (padicIntAbSheaf X l)) :=
  exists_cover_nonempty_iso_padicIntAbSheaf X l G
    (exists_isColimit_cokernelCofork_zmodPowAbSheafDiagram X l) hG hloc haut V

end AlgebraicGeometry.ProEtale
