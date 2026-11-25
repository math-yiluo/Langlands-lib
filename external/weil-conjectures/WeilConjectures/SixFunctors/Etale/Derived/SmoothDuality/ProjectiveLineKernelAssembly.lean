/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.LineDiagonal
public import WeilConjectures.CategoryTheory.Monoidal.KernelAdjunctionTriangle
public import WeilConjectures.EtaleCohomology.Purity.Smooth.ProjectiveLineCohomology
public import WeilConjectures.EtaleCohomology.Purity.Smooth.ProjectiveLineCohomologyChartBoundary
public import WeilConjectures.SixFunctors.Etale.Derived.SmoothDuality.KernelBaseChange
public import WeilConjectures.SixFunctors.Etale.Derived.SmoothDuality.TraceCounitLowerShriek
public import WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal.Braided

/-!
# The projective-line adjunction from a diagonal class

We instantiate the abstract kernel adjunction `CategoryTheory.Adjunction.kernelAdjunction` for
`q : P = ℙ¹_S ⟶ S`, with `W = ℙ¹_P = P ×_S P`, its projections `a = W ↘ P` and `b = map q`, and
the diagonal `Δ : P ⟶ W`:

* `F ⊣ G` is `Lq^* ⊣ Rq_*`, `A ⊣ A'` is `La^* ⊣ Ra_*`, `B ⊣ B'` is `Lb^* ⊣ Rb_*`, `Δ ⊣ Δ'` is
  `LΔ^* ⊣ RΔ_*`;
* `e : Lq^* ⋙ La^* ≅ Lq^* ⋙ Lb^*` and `ι : La^* ⋙ LΔ^* ≅ Lb^* ⋙ LΔ^*` are given by the
  composition isomorphisms (`AlgebraicGeometry.Etale.projectiveLineKernelSquareIso`,
  `AlgebraicGeometry.Etale.projectiveLineKernelDiagonalIso`);
* `τ = Λ_S(1)[2]`, and the trace `Rq_* Lq^* τ ≅ Rq_* Λ_P(1)[2] ⟶ Λ_S` is the trace of the
  projective line;
* the kernel is the kernel `CategoryTheory.Adjunction.kernelOfClass` of a class
  `c : RΔ_* Λ_P ⟶ La^* Lq^* τ`.

The hypotheses on the monoidal structures, on base change and on the projection formulas are
proved; the remaining inputs are the triviality of the braiding of `La^* Lq^* τ` with itself and
the two integrals of the class `c`
(`AlgebraicGeometry.Etale.exists_projectiveLineAdjunction_of_class`). The result is stated in the
form of the counit `AlgebraicGeometry.Etale.lowerShriekTraceCounit`, through
`AlgebraicGeometry.Etale.exists_adjunction_lowerShriek_of_traceCounit`.

## Implementation notes

The trace `t` and the identification `γ` are parameters, so that
`AlgebraicGeometry.Etale.exists_projectiveLineAdjunction` can use
`AlgebraicGeometry.Etale.projectiveLineLowerShriekTrace` and
`AlgebraicGeometry.Etale.projectiveLineTwistShiftIso` themselves: comparing these definitions with
restatements of their bodies makes the kernel time out. The inverse of the projection map in the
conclusion is elaborated with the instances of
`WeilConjectures.SixFunctors.Etale.Derived.SmoothDuality.TraceCounitLowerShriek`; identifying it
with the one of `AlgebraicGeometry.Etale.lowerShriekTraceCounit` by `rfl` still makes the kernel
time out.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory Functor.LaxMonoidal Functor.OplaxMonoidal

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

-- Search the braiding of `ModuleCat Λ` through its symmetric structure and braid étale sheaves
-- through `Etale.sheafBraidedCategory`, as the generic definitions of the derived tensor product
-- do.
attribute [local instance high] SymmetricCategory.toBraidedCategory

attribute [local instance 20000] Etale.sheafBraidedCategory

-- As in `WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionExchange`, so that the
-- generic statements specialise syntactically.
attribute [-instance] CategoryTheory.sheafToPresheaf_isRightAdjoint ModuleCat.hasColimitsOfShape
  ModuleCat.hasColimitsOfSize

attribute [local instance] leftDerivedUpperStarMonoidal _root_.DerivedCategory.braidedCategory'

section General

variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]

/-- The braided structure of the derived pullback: the monoidal structure
`AlgebraicGeometry.Etale.leftDerivedUpperStarMonoidal` with the braided axiom
`AlgebraicGeometry.Etale.leftDerivedUpperStar_μ_map_braiding_hom`. -/
@[instance_reducible]
noncomputable def leftDerivedUpperStarBraidedModuleCat {X Y : Scheme.{u}} (g : X ⟶ Y) :
    (L((g)^*[ModuleCat.{u + 1} Λ])).Braided :=
  { leftDerivedUpperStarMonoidal (ModuleCat.{u + 1} Λ) g with
    braided := leftDerivedUpperStar_μ_map_braiding_hom (ModuleCat.{u + 1} Λ) g }

end General

section TwistShift

variable (Λ : Type (u + 1)) [CommRing Λ] [HasKummerClass Λ] (X : Scheme.{u})

/-- The braiding `M ⊗ᴸ N ≅ N ⊗ᴸ M` as a natural isomorphism `- ⊗ᴸ N ≅ N ⊗ᴸ -`. -/
noncomputable def derivedTensorRightIsoObj
    (N : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    derivedTensorRight (ModuleCat.{u + 1} Λ) X N ≅ (-⊗ᴸ-(X)[ModuleCat.{u + 1} Λ]).obj N :=
  NatIso.ofComponents (fun M ↦ ((derivedTensorBraiding (ModuleCat.{u + 1} Λ) X).app M).app N)
    (fun f ↦
      NatTrans.congr_app ((derivedTensorBraiding (ModuleCat.{u + 1} Λ) X).hom.naturality f) N)

/-- The identification `K(1)[2] ≅ Λ(1)[2] ⊗ᴸ K`, natural in `K`: the shift is moved into the second
factor of `K ⊗ᴸ Λ(1)`, and the factors are exchanged by the braiding. Its components are those of
`AlgebraicGeometry.Etale.projectiveLineTwistShiftIso`. -/
noncomputable def twistShiftOneIsoTensor :
    twistShift Λ X 1 ≅ (-⊗ᴸ-(X)[ModuleCat.{u + 1} Λ]).obj ((tateObject Λ X 1)⟦(2 : ℤ)⟧) :=
  (derivedTensorRightShiftIso (ModuleCat.{u + 1} Λ) (tateObject Λ X 1) 2).symm ≪≫
    derivedTensorRightIsoObj Λ X _

end TwistShift

section ProjectiveLine

variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ] [HasKummerClass Λ]
  [HasKummerClass.IsNormalized Λ] (S : Scheme.{u}) [HasInvertibleExponent Λ S]

set_option hygiene false in
/-- The projective line `P = ℙ¹_S`. -/
local notation "𝐏" => ℙ(Option (ULift.{u} (Fin 1)); S)

set_option hygiene false in
/-- The projective line `W = ℙ¹_P = P ×_S P` over `P = ℙ¹_S`. -/
local notation "𝐖" => ℙ(Option (ULift.{u} (Fin 1)); ℙ(Option (ULift.{u} (Fin 1)); S))

set_option hygiene false in
/-- The second projection `b = map q : W ⟶ P`. -/
local notation "𝐛" => ProjectiveSpace.map (Option (ULift.{u} (Fin 1))) (𝐏 ↘ S)

set_option hygiene false in
/-- The diagonal `Δ : P ⟶ W`. -/
local notation "𝐝" => ProjectiveSpace.diagonal (Option (ULift.{u} (Fin 1))) S

set_option hygiene false in
/-- The object `τ = Λ_S(1)[2]`. -/
local notation "𝛕" => (tateObject Λ S 1)⟦(2 : ℤ)⟧

/-- The isomorphism `e : Lq^* ⋙ La^* ≅ Lq^* ⋙ Lb^*` of the two projections `a = W ↘ P` and
`b = map q` of `W = ℙ¹_P = P ×_S P`, from `b ≫ q = a ≫ q`. -/
noncomputable def projectiveLineKernelSquareIso :
    L(((𝐏 ↘ S))^*[ModuleCat.{u + 1} Λ]) ⋙ L(((𝐖 ↘ 𝐏))^*[ModuleCat.{u + 1} Λ]) ≅
      L(((𝐏 ↘ S))^*[ModuleCat.{u + 1} Λ]) ⋙ L((𝐛)^*[ModuleCat.{u + 1} Λ]) :=
  leftDerivedUpperStarCompSquareIso (ModuleCat.{u + 1} Λ) (𝐖 ↘ 𝐏) 𝐛 (𝐏 ↘ S) (𝐛 ≫ (𝐏 ↘ S))
    (ProjectiveSpace.isPullback_map _ (𝐏 ↘ S)).w rfl

/-- The isomorphism `ι : La^* ⋙ LΔ^* ≅ Lb^* ⋙ LΔ^*`, from `Δ ≫ a = 𝟙 = Δ ≫ b`. -/
noncomputable def projectiveLineKernelDiagonalIso :
    L(((𝐖 ↘ 𝐏))^*[ModuleCat.{u + 1} Λ]) ⋙ L((𝐝)^*[ModuleCat.{u + 1} Λ]) ≅
      L((𝐛)^*[ModuleCat.{u + 1} Λ]) ⋙ L((𝐝)^*[ModuleCat.{u + 1} Λ]) :=
  leftDerivedUpperStarSectionSquareIso (ModuleCat.{u + 1} Λ) (𝐖 ↘ 𝐏) 𝐛 𝐝
    (by rw [ProjectiveSpace.diagonal_over, ProjectiveSpace.diagonal_map])

set_option hygiene false in
/-- The trace `Rq_* Lq^* τ ≅ Rq_* Λ_P(1)[2] ⟶ Λ_S` of the projective line, for `τ = Λ_S(1)[2]`. -/
local notation "𝐭" =>
  ((R(((𝐏 ↘ S))_*[ModuleCat.{u + 1} Λ])).map (leftDerivedUpperStarTateTwoIso Λ (𝐏 ↘ S)).hom ≫
    projectiveLineTrace Λ S :
      (R(((𝐏 ↘ S))_*[ModuleCat.{u + 1} Λ])).obj
        ((L(((𝐏 ↘ S))^*[ModuleCat.{u + 1} Λ])).obj 𝛕) ⟶ 𝟙_ _)

instance isIso_projectiveLineKernelSquareIso_kernelBaseChange
    (M : _root_.DerivedCategory (Sheaf 𝐏.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    IsIso (Adjunction.kernelBaseChange
      (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) (𝐏 ↘ S))
      (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) (𝐖 ↘ 𝐏))
      (projectiveLineKernelSquareIso Λ S) M) :=
  isIso_kernelBaseChange_of_isPullback Λ (ProjectiveSpace.isPullback_map _ (𝐏 ↘ S)) _ _ _ M

instance isIso_projectiveLineKernelSquareIso_symm_kernelBaseChange
    (M : _root_.DerivedCategory (Sheaf 𝐏.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    IsIso (Adjunction.kernelBaseChange
      (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) (𝐏 ↘ S))
      (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) 𝐛)
      (projectiveLineKernelSquareIso Λ S).symm M) := by
  rw [projectiveLineKernelSquareIso, leftDerivedUpperStarCompSquareIso_symm]
  exact isIso_kernelBaseChange_of_isPullback Λ (ProjectiveSpace.isPullback_map _ (𝐏 ↘ S)).flip
    _ _ _ M

/-- The diagonal of the projective line is a closed immersion: it is a section of the separated
morphism `W ↘ P`. -/
instance isClosedImmersion_projectiveLineDiagonal : IsClosedImmersion 𝐝 := by
  have : IsClosedImmersion (𝐝 ≫ (𝐖 ↘ 𝐏)) := by
    rw [ProjectiveSpace.diagonal_over]
    infer_instance
  exact IsClosedImmersion.of_comp 𝐝 (𝐖 ↘ 𝐏)

/-- **The projective-line adjunction from a diagonal class.** Let `c : RΔ_* Λ_P ⟶ La^* Lq^* τ`
be a class (`τ = Λ_S(1)[2]`), with associated cycle class `δ_W : Λ_W ⟶ RΔ_* Λ_P ⟶ La^* Lq^* τ`.
If the braiding of `La^* Lq^* τ` with itself is trivial and the two integrals of `δ_W` (along `a`
against the trace of `a`, and along `b` against the trace of `b`, both obtained from the trace of
`q` by base change) are `1`, then `Rq_!` is left adjoint to `Lq^*(1)[2]`: for every trace
`t : Rq_! Λ(1)[2] ⟶ Λ_S` which is the trace of the projective line through `Rq_! ≅ Rq_*`, and
every `γ : Lq^*(-)(1)[2] ≅ Λ(1)[2] ⊗ᴸ Lq^*(-)`, the counit is
`Rq_!(K(1)[2]) ≅ Rq_!(Λ(1)[2] ⊗ᴸ Lq^* K) ≅ Rq_! Λ(1)[2] ⊗ᴸ K ⟶ Λ_S ⊗ᴸ K ≅ K`. -/
theorem exists_projectiveLineAdjunction_of_class
    (c : (R((𝐝)_*[ModuleCat.{u + 1} Λ])).obj (𝟙_ _) ⟶
      (L(((𝐖 ↘ 𝐏))^*[ModuleCat.{u + 1} Λ])).obj ((L(((𝐏 ↘ S))^*[ModuleCat.{u + 1} Λ])).obj 𝛕))
    (hsymm : (β_ ((L(((𝐖 ↘ 𝐏))^*[ModuleCat.{u + 1} Λ])).obj
        ((L(((𝐏 ↘ S))^*[ModuleCat.{u + 1} Λ])).obj 𝛕))
      ((L(((𝐖 ↘ 𝐏))^*[ModuleCat.{u + 1} Λ])).obj
        ((L(((𝐏 ↘ S))^*[ModuleCat.{u + 1} Λ])).obj 𝛕))).hom = 𝟙 _)
    (hintA : (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) (𝐖 ↘ 𝐏)).unit.app (𝟙_ _) ≫
      (R(((𝐖 ↘ 𝐏))_*[ModuleCat.{u + 1} Λ])).map (η (L(((𝐖 ↘ 𝐏))^*[ModuleCat.{u + 1} Λ])) ≫
        ((derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) 𝐝).unit.app (𝟙_ _) ≫
          (R((𝐝)_*[ModuleCat.{u + 1} Λ])).map (η (L((𝐝)^*[ModuleCat.{u + 1} Λ]))) ≫ c) ≫
        (projectiveLineKernelSquareIso Λ S).hom.app 𝛕) ≫
      Adjunction.kernelTraceA (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) (𝐏 ↘ S))
        (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) (𝐖 ↘ 𝐏))
        (projectiveLineKernelSquareIso Λ S) _ 𝐭 = 𝟙 _)
    (hintB : (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) 𝐛).unit.app (𝟙_ _) ≫
      (R((𝐛)_*[ModuleCat.{u + 1} Λ])).map (η (L((𝐛)^*[ModuleCat.{u + 1} Λ])) ≫
        ((derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) 𝐝).unit.app (𝟙_ _) ≫
          (R((𝐝)_*[ModuleCat.{u + 1} Λ])).map (η (L((𝐝)^*[ModuleCat.{u + 1} Λ]))) ≫ c)) ≫
      Adjunction.kernelTraceA (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) (𝐏 ↘ S))
        (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) 𝐛)
        (projectiveLineKernelSquareIso Λ S).symm _ 𝐭 = 𝟙 _)
    (t : (R((𝐏 ↘ S))_![ModuleCat.{u + 1} Λ]).obj ((tateObject Λ 𝐏 1)⟦(2 : ℤ)⟧) ⟶ 𝟙_ _)
    (ht : (rightDerivedLowerShriekIsoRightDerivedLowerStar (ModuleCat.{u + 1} Λ) (𝐏 ↘ S)).inv.app
        ((tateObject Λ 𝐏 1)⟦(2 : ℤ)⟧) ≫ t =
      (projectiveLineTrace Λ S :
        (R(((𝐏 ↘ S))_*[ModuleCat.{u + 1} Λ])).obj ((tateObject Λ 𝐏 1)⟦(2 : ℤ)⟧) ⟶ 𝟙_ _))
    (γ : L(((𝐏 ↘ S))^*[ModuleCat.{u + 1} Λ]) ⋙ twistShift Λ 𝐏 1 ≅
      L(((𝐏 ↘ S))^*[ModuleCat.{u + 1} Λ]) ⋙
        (-⊗ᴸ-(𝐏)[ModuleCat.{u + 1} Λ]).obj ((tateObject Λ 𝐏 1)⟦(2 : ℤ)⟧)) :
    haveI := isIso_projectionMap_of_finite Λ (𝐏 ↘ S)
    ∃ adj : R((𝐏 ↘ S))_![ModuleCat.{u + 1} Λ] ⊣
        L(((𝐏 ↘ S))^*[ModuleCat.{u + 1} Λ]) ⋙ twistShift Λ 𝐏 1, ∀ K, adj.counit.app K =
      (R((𝐏 ↘ S))_![ModuleCat.{u + 1} Λ]).map (γ.hom.app K) ≫
        inv (((projectionMap (ModuleCat.{u + 1} Λ) (𝐏 ↘ S)).app
          ((tateObject Λ 𝐏 1)⟦(2 : ℤ)⟧)).app K) ≫ t ▷ K ≫ (λ_ K).hom := by
  have htt :
      (R(((𝐏 ↘ S))_*[ModuleCat.{u + 1} Λ])).map (leftDerivedUpperStarTateTwoIso Λ (𝐏 ↘ S)).hom ≫
        (rightDerivedLowerShriekIsoRightDerivedLowerStar (ModuleCat.{u + 1} Λ) (𝐏 ↘ S)).inv.app
          ((tateObject Λ 𝐏 1)⟦(2 : ℤ)⟧) ≫ t = 𝐭 := by
    rw [ht]
  let := leftDerivedUpperStarBraidedModuleCat Λ (𝐖 ↘ 𝐏)
  let adj₀ := Adjunction.kernelAdjunction
    (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) (𝐏 ↘ S))
    (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) (𝐖 ↘ 𝐏))
    (projectiveLineKernelSquareIso Λ S)
    (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) 𝐝)
    (projectiveLineKernelDiagonalIso Λ S)
    (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) 𝐛) 𝛕
    ((R(((𝐏 ↘ S))_*[ModuleCat.{u + 1} Λ])).map (leftDerivedUpperStarTateTwoIso Λ (𝐏 ↘ S)).hom ≫
      (rightDerivedLowerShriekIsoRightDerivedLowerStar (ModuleCat.{u + 1} Λ) (𝐏 ↘ S)).inv.app
        ((tateObject Λ 𝐏 1)⟦(2 : ℤ)⟧) ≫ t)
    (Adjunction.kernelOfClass (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) 𝐝) c)
    ((derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) 𝐝).unit.app (𝟙_ _) ≫
      (R((𝐝)_*[ModuleCat.{u + 1} Λ])).map (η (L((𝐝)^*[ModuleCat.{u + 1} Λ]))) ≫ c)
    (map_μ_comp_leftDerivedUpperStarCompSquareIso_hom_app _ _ _ _ _ _ _)
    (leftDerivedUpperStarCompSquareIso_hom_app_tensorUnit_comp_η _ _ _ _ _ _ _)
    (leftDerivedUpperStarSectionSquareIso_hom_app_tensor _ _ _ _ _)
    (leftDerivedUpperStarSectionSquareIso_hom_app_obj _ _ _ _ _ _ _ _ _)
    (Adjunction.kernelOfClass_linear _ c)
    (Adjunction.unit_app_comp_kernelOfClass_app _ c _) hsymm (by rw [htt]; exact hintA)
    (by rw [htt]; exact hintB)
  exact exists_adjunction_lowerShriek_of_traceCounit Λ (𝐏 ↘ S) ((tateObject Λ 𝐏 1)⟦(2 : ℤ)⟧)
    ((L(((𝐏 ↘ S))^*[ModuleCat.{u + 1} Λ])).obj 𝛕)
    (leftDerivedUpperStarTateTwoIso Λ (𝐏 ↘ S)) t γ adj₀ (Adjunction.kernelAdjunction_counit ..)

end ProjectiveLine

end Etale

end AlgebraicGeometry
