/-
Copyright (c) 2026 The Weil Conjectures contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.WeilSheaf.SmoothPurityIntegralTateReductionPullback
public import WeilConjectures.WeilSheaf.SmoothPurityTensorComparison
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.PullIsoMonoidal

/-! # Finite coefficient reductions of all nonnegative Tate powers -/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

open Scheme CondensedRing

variable (ℓ : ℕ) [Fact ℓ.Prime] (E : Type) [Field E] [Algebra E (PadicAlgCl ℓ)]
  [Algebra ℚ_[ℓ] E] [IsScalarTower ℚ_[ℓ] E (PadicAlgCl ℓ)] (n : ℕ)

/-- The finite Tate line as the free coefficient module on the roots of unity. -/
noncomputable def purityFiniteTateLine (X : Scheme.{u}) :=
  (Mod.freeFunctor (condensedRingObj (Profinite.integersModPowRingObj ℓ E n) X)).obj
    (rootsOfUnitySheaf X (ℓ ^ n))

/-- Tensor powers of the finite Tate line in the condensed module model. -/
noncomputable def purityFiniteTatePower (X : Scheme.{u}) :
    ℕ → Mod (Sheaf (ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.integersModPowRingObj ℓ E n) X)
  | 0 => 𝟙_ _
  | d + 1 => purityFiniteTatePower X d ⊗ purityFiniteTateLine ℓ E n X

variable {k : Type u} [Field k] [NeZero (ℓ : k)] {X X' : Scheme.{u}}

/-- Pullback of the finite Tate line through the actual roots-of-unity comparison. -/
noncomputable def purityFiniteTateLinePullbackIso (g : X' ⟶ X) (f : X ⟶ Spec (.of k)) :
    (g)^*⟦Profinite.integersModPowRingObj ℓ E n⟧.obj (purityFiniteTateLine ℓ E n X) ≅
      purityFiniteTateLine ℓ E n X' :=
  (freeFunctorCompUpperStarIso (Profinite.integersModPowRingObj ℓ E n) g).app _ ≪≫
    (Mod.freeFunctor _).mapIso (purityTateRootPullbackIso ℓ g f n)

/-- Pullback of finite Tate powers using the canonical monoidal structure. -/
noncomputable def purityFiniteTatePowerPullbackIso (g : X' ⟶ X) (f : X ⟶ Spec (.of k)) :
    (d : ℕ) → (g)^*⟦Profinite.integersModPowRingObj ℓ E n⟧.obj
      (purityFiniteTatePower ℓ E n X d) ≅ purityFiniteTatePower ℓ E n X' d
  | 0 => (Functor.Monoidal.εIso _).symm
  | d + 1 => (Functor.Monoidal.μIso _ _ _).symm ≪≫
      (purityFiniteTatePowerPullbackIso g f d ⊗ᵢ purityFiniteTateLinePullbackIso ℓ E n g f)

/-- The actual reduction of an integral Tate power to the corresponding finite power. -/
noncomputable def purityReduceIntegralTatePowerIso (f : X ⟶ Spec (.of k)) :
    (d : ℕ) → (Mod.extendScalars (integersModPowReduction X ℓ E n)).obj
      (integralTateTwistNat X ℓ E d) ≅ purityFiniteTatePower ℓ E n X d
  | 0 =>
      letI := Mod.extendScalarsMonoidal (integersModPowReduction X ℓ E n)
      (Functor.Monoidal.εIso _).symm
  | d + 1 =>
      letI := Mod.extendScalarsMonoidal (integersModPowReduction X ℓ E n)
      (Functor.Monoidal.μIso _ _ _).symm ≪≫
        (purityReduceIntegralTatePowerIso f d ⊗ᵢ
          extendScalarsIntegralTateTwistOneIntegersModPowIso ℓ E n f)

/-- Reduction carries the canonical integral Tate datum to the finite root datum,
for every nonnegative power. -/
lemma upperStarIntegralTateTwistNatIso_hom_comp_reduction
    (g : X' ⟶ X) (f : X ⟶ Spec (.of k)) (d : ℕ) :
    (pullIso (Profinite.padicIntegersRingObjToIntegersModPow ℓ E n) g).inv.app
          (integralTateTwistNat X ℓ E d) ≫
        (Mod.extendScalars (integersModPowReduction X' ℓ E n)).map
          (upperStarIntegralTateTwistNatIso ℓ E g f d).hom ≫
        (purityReduceIntegralTatePowerIso ℓ E n (g ≫ f) d).hom =
      (g)^*⟦Profinite.integersModPowRingObj ℓ E n⟧.map
          (purityReduceIntegralTatePowerIso ℓ E n f d).hom ≫
        (purityFiniteTatePowerPullbackIso ℓ E n g f d).hom := by
  let a := Profinite.padicIntegersRingObjToIntegersModPow ℓ E n
  let := Mod.extendScalarsMonoidal (coefficientMap a X)
  let := Mod.extendScalarsMonoidal (coefficientMap a X')
  have : NatTrans.IsMonoidal (pullIso a g).hom := isMonoidal_pullIso_hom a g
  induction d with
  | zero =>
      exact purity_unit_comparison
        (g)^*⟦Profinite.padicIntegersRingObj ℓ E⟧
        (Mod.extendScalars (coefficientMap a X'))
        (Mod.extendScalars (coefficientMap a X))
        (g)^*⟦Profinite.integersModPowRingObj ℓ E n⟧ (pullIso a g).inv
  | succ d ih =>
      exact purity_tensor_comparison
        (g)^*⟦Profinite.padicIntegersRingObj ℓ E⟧
        (Mod.extendScalars (coefficientMap a X'))
        (Mod.extendScalars (coefficientMap a X))
        (g)^*⟦Profinite.integersModPowRingObj ℓ E n⟧ (pullIso a g).inv
        (upperStarIntegralTateTwistNatIso ℓ E g f d).hom
        (upperStarIntegralTateTwistOneIso ℓ E g f).hom
        (purityReduceIntegralTatePowerIso ℓ E n f d).hom
        (extendScalarsIntegralTateTwistOneIntegersModPowIso ℓ E n f).hom
        (purityFiniteTatePowerPullbackIso ℓ E n g f d).hom
        (purityFiniteTateLinePullbackIso ℓ E n g f).hom
        (purityReduceIntegralTatePowerIso ℓ E n (g ≫ f) d).hom
        (extendScalarsIntegralTateTwistOneIntegersModPowIso ℓ E n (g ≫ f)).hom ih
        (upperStarIntegralTateTwistOneIso_hom_comp_reduction ℓ E g f n)

end AlgebraicGeometry.ProEtale
