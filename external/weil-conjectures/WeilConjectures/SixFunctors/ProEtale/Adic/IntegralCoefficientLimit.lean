/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic
public import Mathlib.Topology.Instances.ZMod
public import WeilConjectures.CategoryTheory.RingObjects.EllAdic
public import WeilConjectures.SixFunctors.ProEtale.Adic.IntegralCoefficients

/-!
# `ℤ_ℓ,X` is the limit of the constant sheaves `(ℤ/ℓⁿ)_X`

Let `X` be a scheme and `ℓ` a prime. On the small pro-étale site of `X`, the sheaf of rings
`ℤ_ℓ,X = C(-, ℤ_ℓ)` (`AlgebraicGeometry.ProEtale.padicIntSheaf`) is the limit of the sheaves of
rings `(ℤ/ℓⁿ)_X = C(-, ℤ/ℓⁿ)` of locally constant functions, along the reductions
(`AlgebraicGeometry.ProEtale.isLimitPadicIntSheafCone`). This is
`lemma-comparison-completed-coefficients--1` (3) for `E = ℚ_ℓ`; the limit is computed
sectionwise, where it is `C(U, ℤ_ℓ) = lim_n C(U, ℤ/ℓⁿ)`
(`PadicInt.continuousMapRingEquivCompatibleLocallyConstant`).

## Main definitions

- `AlgebraicGeometry.ProEtale.zmodPowSheafDiagram`: the tower `n ↦ (ℤ/ℓⁿ)_X` of sheaves of rings.
- `AlgebraicGeometry.ProEtale.padicIntSheafCone`: the cone of reductions `ℤ_ℓ,X → (ℤ/ℓⁿ)_X`.
- `AlgebraicGeometry.ProEtale.isLimitPadicIntSheafCone`: it is a limit cone.
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry.ProEtale

open Scheme

variable (X : Scheme.{u}) (l : ℕ) [Fact l.Prime]

/-- The tower `n ↦ (ℤ/ℓⁿ)_X` of sheaves of rings `U ↦ C(U, ℤ/ℓⁿ)` of locally constant
functions on `X_proét`, with the reductions as transition maps. -/
noncomputable def zmodPowSheafDiagram : ℕᵒᵖ ⥤ Sheaf (ProEt.topology X) RingCat.{u + 1} where
  obj n := continuousMapRingSheaf X (ZMod (l ^ n.unop))
  map h := continuousMapRingSheafMap X (ZMod.castHom (pow_dvd_pow l (leOfHom h.unop)) _)
    continuous_of_discreteTopology
  map_id n := by
    refine ObjectProperty.hom_ext _ (NatTrans.ext (funext fun U ↦ RingCat.hom_ext
      (RingHom.ext fun g ↦ ULift.ext (ContinuousMap.ext fun t ↦ ?_))))
    exact RingHom.congr_fun ZMod.castHom_self _
  map_comp f g := by
    refine ObjectProperty.hom_ext _ (NatTrans.ext (funext fun U ↦ RingCat.hom_ext
      (RingHom.ext fun x ↦ ULift.ext (ContinuousMap.ext fun t ↦ ?_))))
    exact RingHom.congr_fun (ZMod.castHom_comp
      (pow_dvd_pow l (leOfHom g.unop)) (pow_dvd_pow l (leOfHom f.unop))).symm _

/-- The cone of reductions `ℤ_ℓ,X → (ℤ/ℓⁿ)_X`. -/
noncomputable def padicIntSheafCone : Cone (zmodPowSheafDiagram X l) where
  pt := padicIntSheaf X l
  π :=
    { app n := continuousMapRingSheafMap X (PadicInt.toZModPow n.unop)
        (PadicInt.isLocallyConstant_toZModPow n.unop).continuous
      naturality m n h := by
        refine ObjectProperty.hom_ext _ (NatTrans.ext (funext fun U ↦ RingCat.hom_ext
          (RingHom.ext fun x ↦ ULift.ext (ContinuousMap.ext fun t ↦ ?_))))
        exact RingHom.congr_fun
          (PadicInt.zmod_cast_comp_toZModPow _ _ (leOfHom h.unop)).symm _ }

/-- The compatible family of locally constant functions `U → ℤ/ℓⁿ` underlying a compatible
family of sections of the `(ℤ/ℓⁿ)_X` over `U`. -/
noncomputable def compatibleLocallyConstantOfSection (U : X.ProEtᵒᵖ)
    {s : ∀ n : ℕᵒᵖ, ULift.{u + 1} C(U.unop.left, ZMod (l ^ n.unop))}
    (hs : s ∈ (((zmodPowSheafDiagram X l ⋙ sheafToPresheaf _ _) ⋙
      (CategoryTheory.evaluation _ _).obj U) ⋙ forget RingCat.{u + 1}).sections) :
    PadicInt.compatibleLocallyConstant l U.unop.left :=
  ⟨fun n ↦ ⟨fun t ↦ (s (op n)).down t,
      (IsLocallyConstant.iff_continuous _).2 (s (op n)).down.continuous⟩,
    fun m _ h t ↦ congrArg (fun g : ULift.{u + 1} C(U.unop.left, ZMod (l ^ m)) ↦ g.down t)
      (hs (homOfLE h).op)⟩

/-- Over every `U`, the continuous functions `U → ℤ_ℓ` are the compatible families of continuous
(i.e. locally constant) functions `U → ℤ/ℓⁿ`: `padicIntSheafCone` is sectionwise a limit cone
of sets. -/
lemma nonempty_isLimit_mapCone_padicIntSheafCone (U : X.ProEtᵒᵖ) :
    Nonempty (IsLimit ((forget RingCat.{u + 1}).mapCone
      (((CategoryTheory.evaluation _ _).obj U).mapCone
        ((sheafToPresheaf _ _).mapCone (padicIntSheafCone X l))))) := by
  refine (Types.isLimit_iff _).2 fun s hs ↦ ?_
  let a := compatibleLocallyConstantOfSection X l U (s := s) hs
  refine ⟨ULift.up (PadicInt.compatibleLocallyConstantToContinuousMap a), fun j ↦ ULift.ext
    (ContinuousMap.ext fun t ↦
      (PadicInt.toZModPow_ringEquivCompatibleFamilies_symm _ _).trans (by rfl)), fun y hy ↦ ?_⟩
  refine ULift.ext (ContinuousMap.ext fun t ↦ PadicInt.ext_of_toZModPow.1 fun n ↦ ?_)
  exact (congrArg (fun g : ULift.{u + 1} C(U.unop.left, ZMod (l ^ n)) ↦ g.down t)
    (hy (op n))).trans (PadicInt.toZModPow_ringEquivCompatibleFamilies_symm
      (PadicInt.compatibleLocallyConstantEval t a) n).symm

/-- **`ℤ_ℓ,X = lim_n (ℤ/ℓⁿ)_X`** as sheaves of rings on `X_proét`
(`lemma-comparison-completed-coefficients--1` (3), for `E = ℚ_ℓ`): the limit is computed
sectionwise, where it is `C(U, ℤ_ℓ) = lim_n C(U, ℤ/ℓⁿ)`. -/
noncomputable def isLimitPadicIntSheafCone : IsLimit (padicIntSheafCone X l) := by
  have : ReflectsLimitsOfSize.{0, 0} (forget RingCat.{u + 1}) :=
    reflectsLimits_of_reflectsIsomorphisms
  exact isLimitOfReflects (sheafToPresheaf _ _) (evaluationJointlyReflectsLimits _ fun U ↦
    isLimitOfReflects (forget RingCat.{u + 1})
      (nonempty_isLimit_mapCone_padicIntSheafCone X l U).some)

/-- The inclusion `ℤ_ℓ,X → ℚ̄_ℓ,X` of the integral functions into the constant `ℓ`-adic sheaf
`AlgebraicGeometry.ProEtale.adicConstantSheaf` underlying `ℓ`-adic sheaves, as a morphism of
abelian sheaves: the map along which an integral lattice `lim_n Fₙ` of a lisse sheaf is to be
rationalised. -/
noncomputable def integralToAdicConstantSheaf :
    (sheafCompose (ProEt.topology X) (forget₂ RingCat.{u + 1} Ab.{u + 1})).obj
        (padicIntSheaf X l) ⟶
      (sheafCompose (ProEt.topology X) (forget₂ (WeilCoefficients.{u} l) Ab.{u + 1})).obj
        (adicConstantSheaf l X) :=
  ObjectProperty.homMk
    { app U := AddCommGrpCat.ofHom
        { toFun x := ULift.up (PadicAlgCl.integralToLocallyFiniteFunctions l U.unop.left x.down)
          map_zero' := congrArg ULift.up (map_zero _)
          map_add' x y := congrArg ULift.up (map_add _ x.down y.down) }
      naturality _ _ _ := rfl }

end AlgebraicGeometry.ProEtale
