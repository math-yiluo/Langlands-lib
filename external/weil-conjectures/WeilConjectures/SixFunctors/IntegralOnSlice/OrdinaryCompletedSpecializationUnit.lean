/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.IntegralOnSlice.QcqsCompletionOrdinaryModels
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import WeilConjectures.SixFunctors.IntegralOnSlice.QcqsOrdinaryRestrictionExact
import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleAbelianSpecializationOfUniverses
import WeilConjectures.AlgebraicGeometry.ProEtale.Module.ProEtaleModuleUnitFromAbelianOfUniverses

/-! # Completed module units on closed specialization neighbourhoods

Source: Stacks Project, Pro-etale Cohomology, Tag 09AC; Modules on Sites, Tags 03D2 and 03D3.
(blueprint: lem-fix-ordinary-completed-specialization-unit).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
universe t u v w
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.IntegralOnSlice

private instance abelianWeakSheafify (Z : Scheme.{t}) :
    HasWeakSheafify (ProEt.topology Z) AddCommGrpCat.{max u (t + 1)} :=
  (integralCoefficientAbSheafify.{t, u} Z).isRightAdjoint

private abbrev abelianPush {X Y : Scheme.{t}} (f : X ⟶ Y) :=
  (proEtaleBaseChange f).sheafPushforwardContinuous AddCommGrpCat.{max u (t + 1)}
    (ProEt.topology Y) (ProEt.topology X)

private theorem abelianPush_isRightAdjoint {X Y : Scheme.{t}} (f : X ⟶ Y) :
    (abelianPush.{t, u} f).IsRightAdjoint := by
  let : HasColimitsOfSize.{t + 1, t + 1} AddCommGrpCat.{max u (t + 1)} :=
    hasColimitsOfSizeShrink.{t + 1, t + 1, max u (t + 1), max u (t + 1)} _
  let : EssentiallySmall.{t + 1} Y.ProEt := essentiallySmallSelf.{0} _
  let : LocallySmall.{t + 1} X.ProEt := ⟨fun _ _ ↦ inferInstance⟩
  have : ∀ V : X.ProEtᵒᵖ,
      HasColimitsOfShape (CostructuredArrow (proEtaleBaseChange f).op V)
        AddCommGrpCat.{max u (t + 1)} := fun _ ↦
    hasColimitsOfShape_of_essentiallySmall.{t + 1} _ _
  have : ∀ F : Y.ProEtᵒᵖ ⥤ AddCommGrpCat.{max u (t + 1)},
      (proEtaleBaseChange f).op.HasLeftKanExtension F := fun _ ↦ inferInstance
  exact (Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
    (proEtaleBaseChange f) AddCommGrpCat.{max u (t + 1)}
      (ProEt.topology Y) (ProEt.topology X)).isRightAdjoint

/-- On a weakly contractible affine whose points specialize to the closed fibre,
the actual ordinary completed-module adjunction unit is bijective on sections.

Source: Stacks Project, Pro-etale Cohomology, Tag 09AC (lemma-compute-i-star),
Modules on Sites, Tags 03D2 and 03D3.
(blueprint: lem-fix-ordinary-completed-specialization-unit).

Proof: restrict to the affine scheme V.left using the equivalence of its pro-etale
site with the site localized at V. The affine closed-site functors v and u satisfy
v adjoint to u, with v fully faithful. The counit at V contains the closed fibre
in its image; flat going-down and the specialization assumption imply that this
image is all of V. Weak contractibility splits this cover. Full faithfulness and
the adjunction show that the splitting is its inverse. Covers of the closed fibre
lift through v to covers of V and similarly split. Thus inverse image to the
closed fibre, evaluated on that fibre, is naturally evaluation at V. This
identification carries the abelian inverse-image unit to the identity.
The same assertion holds for module inverse image: transport scalar multiplication
through the coefficient inverse-image isomorphism, and use the unit equations in
the underlying abelian inverse-image adjunction. The completed coefficient map is
invertible for the closed immersion by qcqsOrdinaryRestrictionExact, and the
finite-projection characterization identifies its adjoint with
ordinaryCompletedRingMap. Uniqueness of left adjoints then identifies this unit
with the specified ordinaryAdjunction unit, up to an invertible map on its target.
All sheaves and module presentations are taken in max u (t+1). The localized
sites have size at most t+1, so sheafification exists there; no equality between
the coefficient-field and scheme universes is used. Empty V gives singleton
section modules and hence the same bijectivity assertion. -/
theorem ordinaryCompletedSpecializationUnit
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    {X Z : Scheme.{t}} [CompactSpace X] [QuasiSeparatedSpace X]
    [CompactSpace Z] [QuasiSeparatedSpace Z]
    (i : Z ⟶ X) [IsClosedImmersion i]
    (V : X.ProEt) [IsAffine V.left]
    (hweak : ∀ (P Q : Sheaf (ProEt.topology X) (Type (max u (t + 1)))) (φ : P ⟶ Q),
      Epi φ → Function.Surjective (φ.hom.app (op V)))
    (hspec : ∀ x : V.left, ∃ z : ↥(pullback V.hom i),
      Specializes x ((pullback.fst V.hom i) z))
    (M : Mod l E X none) :
    Function.Bijective (((ordinaryAdjunction l E i).unit.app M).val.app (op V)) := by
  have hc : IsIso (ordinaryCoefficientMap l E i) := by
    exact (congrArg (fun f : Z ⟶ X ↦ IsIso (ordinaryCoefficientMap l E f))
      (Category.id_comp i)) ▸ (qcqsOrdinaryRestrictionExact l E (𝟙 Z) i).2
  have : IsIso
      (((Adjunction.ofIsRightAdjoint (ordinaryRingPush.{t, u} i)).homEquiv
        (completedIntegralCoefficientSheafUnrestricted l E X)
        (completedIntegralCoefficientSheafUnrestricted l E Z)).symm
          (ordinaryCompletedRingMap l E i)) := hc
  let := abelianPush_isRightAdjoint.{t, u} i
  let B := (abelianPush.{t, u} i).leftAdjoint
  let aB := Adjunction.ofIsRightAdjoint (abelianPush.{t, u} i)
  exact proEtale_module_unit_bijective_of_abelian i V
    (completedIntegralCoefficientSheafUnrestricted l E X)
    (completedIntegralCoefficientSheafUnrestricted l E Z)
    (ordinaryCompletedRingMap l E i) (ordinaryRingInverse.{t, u} i)
    (Adjunction.ofIsRightAdjoint (ordinaryRingPush.{t, u} i)) B aB
    (ordinaryPull l E i) (ordinaryAdjunction l E i) M
    (proEtale_abelian_unit_bijective_of_specialization i V hweak hspec B aB
      ((SheafOfModules.toSheaf _).obj M))

end WeilConjectures.IntegralOnSlice
