/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.IntegralConstantModelRealization
public import WeilConjectures.AlgebraicGeometry.IntegralModelsStacksData
import all WeilConjectures.AlgebraicGeometry.ConstantCompletionInverseImage
import all WeilConjectures.AlgebraicGeometry.IntegralModelsEmbeddedCompletion
import WeilConjectures.AlgebraicGeometry.IntegralModelsFlatResidue
import all WeilConjectures.AlgebraicGeometry.OrdinaryCommonQuotientTower
import all WeilConjectures.CategoryTheory.InternalSectionScalarAdjunction
import WeilConjectures.SixFunctors.ProEtale.InternalFirstResidueRingPushout
import WeilConjectures.CategoryTheory.ModuleObjects.MapMod
public import WeilConjectures.Algebra.Homology.OrdinaryCommonQuotientTower.OrdinaryCommonQuotientTowerSupplement
public import WeilConjectures.AlgebraicGeometry.Constant.ConstantCompletionInverseImageSupplement
public import WeilConjectures.AlgebraicGeometry.Integral.Constant.IntegralConstantModelRealizationSupplement
public import WeilConjectures.CategoryTheory.SixFunctors.InternalSectionScalarAdjunctionSupplement
public import WeilConjectures.SixFunctors.ProEtale.InternalCompletionSectionTransport
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Continuous.ContinuousCoefficientModuleEncodingSupplement
public import WeilConjectures.SixFunctors.Supporting.ConstantCompletionEquivalence

/-! # The ordinary common first-residue tensor comparison -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale

attribute [local irreducible] upperStarFromPoint

local instance ordinaryResidueSiteSmall (X : Scheme.{u}) : EssentiallySmall.{u + 1} X.ProEt :=
  essentiallySmallSelf.{0, u, u + 1} _

local instance ordinaryResidueAbSheafify (X : Scheme.{u}) :
    HasSheafify (Scheme.ProEt.topology X) AddCommGrpCat.{u + 1} :=
  WeilConjectures.integralCoefficientAbSheafify.{u, u} X

local instance ordinaryResidueAbLocallyBijective (X : Scheme.{u}) :
    (Scheme.ProEt.topology X).WEqualsLocallyBijective AddCommGrpCat.{u + 1} :=
  WeilConjectures.integralCoefficientAbLocallyBijective.{u, u} X

private def smallRestrictionIso (X : Scheme.{u})
    {R S : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}}
    [MonObj R] [MonObj S] [IsCommMonObj R] [IsCommMonObj S]
    (f : R ⟶ S) [IsMonHom f] :
    Mod.comap f ⋙ IntegralModelsStacks.smallModules X R ≅
      IntegralModelsStacks.smallModules X S ⋙
        ConstantCompletion.res (IntegralModelsStacks.smallMap X f) := by
  dsimp only [IntegralModelsStacks.smallModules, IntegralModelsStacks.smallMap]
  let e := AlgebraicGeometry.ProEtale.CondensedRing.sectionModuleComapIso X f
  refine NatIso.ofComponents (fun M ↦ ?_) ?_
  · refine (SheafOfModules.fullyFaithfulForget _).preimageIso
      (PresheafOfModules.isoMk (fun U ↦ ?_) ?_)
    · refine ModuleCat.isoMk (Iso.refl _) ?_
      intro r
      ext m
      exact (((e.hom.app M).val.app (Opposite.op (AsSmall.down.obj U.unop))).hom.map_smul r m).symm
    · intro U V g
      ext m
      rfl
  · intro M N g
    ext U m
    rfl

private def ordinarySmallExtensionIso (X : Scheme.{u})
    {R S : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}}
    [MonObj R] [MonObj S] [IsCommMonObj R] [IsCommMonObj S]
    (f : R ⟶ S) [IsMonHom f] :
    Mod.extendScalars f ⋙ IntegralModelsStacks.smallModules X S ≅
      IntegralModelsStacks.smallModules X R ⋙
        ConstantCompletion.change (IntegralModelsStacks.smallMap X f) := by
  have : (IntegralModelsStacks.smallModules X R).IsEquivalence :=
    smallModulesEquivalence X R
  have : (IntegralModelsStacks.smallModules X S).IsEquivalence :=
    smallModulesEquivalence X S
  let adj := SheafOfModules.RingedTensor.tensorAdjunction
    (IntegralModelsStacks.smallMap X f)
  let β := smallRestrictionIso X f
  let α := ((mateEquiv (Mod.extendRestrictAdjunction f) adj).symm
    (TwoSquare.mk _ _ _ _ β.hom))
  have : IsIso α := InternalAbelianSheafModule.inverseMate_isIso
    (Mod.extendRestrictAdjunction f) adj β
  exact (asIso α).symm

private theorem ordinarySmallPushoutIso (X : Scheme.{u})
    {R B S : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}}
    [MonObj R] [MonObj B] [MonObj S]
    [IsCommMonObj R] [IsCommMonObj B] [IsCommMonObj S]
    (f : R ⟶ B) [IsMonHom f] (q : R ⟶ S) [IsMonHom q]
    (p : B ⟶ S) [IsMonHom p]
    (h : IsPushout (IntegralModelsStacks.smallMap X f)
      (IntegralModelsStacks.smallMap X q) (IntegralModelsStacks.smallMap X p) (𝟙 _)) :
    Nonempty (Mod.comap f ⋙ Mod.extendScalars q ≅ Mod.extendScalars p) := by
  classical
  let F := IntegralModelsStacks.smallModules X S
  have : F.IsEquivalence := smallModulesEquivalence X S
  let f' := IntegralModelsStacks.smallMap X f
  let q' := IntegralModelsStacks.smallMap X q
  let p' := IntegralModelsStacks.smallMap X p
  let := HasDerivedCategory.standard (ConstantCompletion.Mod
    (IntegralModelsStacks.smallRing X R))
  let := HasDerivedCategory.standard (ConstantCompletion.Mod
    (IntegralModelsStacks.smallRing X B))
  let := HasDerivedCategory.standard (ConstantCompletion.Mod
    (IntegralModelsStacks.smallRing X S))
  obtain ⟨A⟩ := SheafOfModules.nonempty_derivedChangeOfRingsCochainModel q'
  obtain ⟨B'⟩ := SheafOfModules.nonempty_derivedChangeOfRingsCochainModel p'
  obtain ⟨γ, _⟩ := SheafOfModules.ordinaryComparison f' q' p' h A B'
  let iA : A.E ≅ ConstantCompletion.change q' :=
    SheafOfModules.ordinaryModelIso q' _ _ A.obj_eq (fun _ ↦ rfl)
      (fun g ↦ A.map_eq g) (fun g ↦ by simp; rfl)
  let iB : B'.E ≅ ConstantCompletion.change p' :=
    SheafOfModules.ordinaryModelIso p' _ _ B'.obj_eq (fun _ ↦ rfl)
      (fun g ↦ B'.map_eq g) (fun g ↦ by simp; rfl)
  let δ := Functor.isoWhiskerLeft (ConstantCompletion.res f') iA.symm ≪≫ γ ≪≫ iB
  refine ⟨Functor.fullyFaithfulCancelRight F ?_⟩
  exact Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (Mod.comap f) (ordinarySmallExtensionIso X q) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (smallRestrictionIso X f) (ConstantCompletion.change q') ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (IntegralModelsStacks.smallModules X B) δ ≪≫
    (ordinarySmallExtensionIso X p).symm

private theorem ordinaryScalarFlat
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] (X : Scheme.{u}) :
    PreservesFiniteLimits (Mod.extendScalars (IntegralModelsStacks.scalarMap l E X)) := by
  let f := IntegralModelsStacks.scalarMap l E X
  let R := (upperStarFromPoint X).obj
    (IntegralModelsStacks.discreteObj (Padic.coefficientExtensionIntegers l E))
  let S := (upperStarFromPoint X).obj (IntegralModelsStacks.integersObj l E)
  have : (IntegralModelsStacks.smallModules X R).IsEquivalence :=
    smallModulesEquivalence X R
  have : (IntegralModelsStacks.smallModules X S).IsEquivalence :=
    smallModulesEquivalence X S
  have hflat := (IntegralModelsStacks.integralModels_flat_residue l E X).2.1
  have : PreservesFiniteLimits
      (ConstantCompletion.change (IntegralModelsStacks.smallMap X f)) :=
    (ConstantCompletion.change_exact _ hflat).1
  have : PreservesFiniteLimits
      (Mod.extendScalars f ⋙ IntegralModelsStacks.smallModules X S) :=
    preservesFiniteLimits_of_natIso (ordinarySmallExtensionIso X f).symm
  exact preservesFiniteLimits_of_reflects_of_preserves _
    (IntegralModelsStacks.smallModules X S)

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
  WeilConjectures.integralCoefficientAbLocallyBijective
  WeilConjectures.integralCoefficientAbSheafify WeilConjectures.integralCoefficientRingSheafify in
/-- The constant-to-continuous integral map is flat and its ordinary first-residue
extension is the continuous first-residue extension, followed by residue restriction.
Source: integral-models proof (1)--(2), Stacks Tags 099L and 08FZ.
(auxiliary; not a blueprint node).

Proof: write A = O_E and k = A/(pi). The constant-function map to continuous
k-valued sections is locally bijective, using the finite clopen cover by fibres.
For an empty object use the empty cover. Sheafification gives a ring isomorphism;
let e be its inverse. Naturality of constant functions identifies the quotient
maps. Identify the continuous integral ring with the inverse limit of its finite
quotients by the projection-normalized integral coefficient comparison. The
constant-to-completed scalar map is flat by integral_constant_completion (Stacks
099L). Its first quotient is k, and the ordinary common-quotient tensor comparison
is the isomorphism sending s tensor m to s tensor m. The inverse is well-defined
by the same quotient relation. Transport this ordinary comparison through the
exact section-module equivalence and the equivalent coefficient-sized small site.
Finally pointComparison reconciles the two integral topologies. These transports
preserve finite limits and the tensor comparison is natural in the module. No
complexes or derived localization occur in this assertion. -/
theorem internal_first_residue_ordinary_comparison
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] (X : Scheme.{u}) :
    let a := IntegralModelsStacks.scalarMap l E X ≫
      coefficientMap (IntegralConstantModel.pointComparison l E).inv.hom X
    ∃ e : Mon.mk (DerivedNakayama.quotientRing l E 1) ≅
        Mon.mk (IntegralModelsStacks.discreteObj (Padic.coefficientExtensionRing l E 1)),
      PreservesFiniteLimits (Mod.extendScalars a) ∧
      Nonempty
        (Mod.comap a ⋙ Mod.extendScalars (IntegralModelsStacks.residueMap l E X) ≅
          Mod.extendScalars (AdicCompletion.quotient l E X 0) ⋙
            Mod.comap (coefficientMap e.inv.hom X)) := by
  obtain ⟨e, hpush⟩ := internal_first_residue_ring_pushout l E X
  let f := IntegralModelsStacks.scalarMap l E X
  let g := coefficientMap (IntegralConstantModel.pointComparison l E).inv.hom X
  let a := f ≫ g
  let q := AdicCompletion.quotient l E X 0
  let i := coefficientMap e.hom.hom X
  let j := coefficientMap e.inv.hom X
  have : PreservesFiniteLimits (Mod.extendScalars f) := ordinaryScalarFlat l E X
  have : PreservesFiniteLimits
      (Mod.comap (D := Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (asIso g).inv) :=
    inferInstance
  have : PreservesFiniteLimits (Mod.extendScalars g) :=
    preservesFiniteLimits_of_natIso (Mod.extendScalarsIsoComapInv g).symm
  have : PreservesFiniteLimits (Mod.extendScalars a) :=
    preservesFiniteLimits_of_natIso (Mod.extendScalarsComp f g).symm
  obtain ⟨γ⟩ := ordinarySmallPushoutIso X a
    (IntegralModelsStacks.residueMap l E X) (q ≫ i) hpush
  have hi : (asIso i).inv = j := by
    apply IsIso.inv_eq_of_hom_inv_id
    change (upperStarFromPoint X).map e.hom.hom ≫
      (upperStarFromPoint X).map e.inv.hom = 𝟙 _
    rw [← Functor.map_comp]
    exact (congrArg ((upperStarFromPoint X).map)
      (congrArg (fun h ↦ h.hom) e.hom_inv_id)).trans ((upperStarFromPoint X).map_id _)
  refine ⟨e, inferInstance, ⟨γ ≪≫ Mod.extendScalarsComp q i ≪≫ ?_⟩⟩
  exact Functor.isoWhiskerLeft (Mod.extendScalars q)
    (Mod.extendScalarsIsoComapInv i ≪≫ Mod.comapCongr hi)

end AlgebraicGeometry.ProEtale
