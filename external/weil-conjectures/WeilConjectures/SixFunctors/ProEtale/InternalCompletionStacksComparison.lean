/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.IntegralConstantModelRealization
public import WeilConjectures.AlgebraicGeometry.IntegralModelsStacksData
import WeilConjectures.SixFunctors.ProEtale.InternalConstantResidueGenerator
import WeilConjectures.SixFunctors.ProEtale.InternalQuotientKoszulUnitComparison

/-! # Actual Roos completeness and constant-coefficient completeness

Source: integral-models proof (1), Stacks Tags 099I, 099L and 099M.
(auxiliary; not a blueprint node).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] AlgebraicGeometry.ProEtale.upperStarFromPoint
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale

/-- The canonical scalar restriction identifies the actual Roos completeness predicate.
Source: integral-models proof (1); constant-coefficient criterion proof (2)--(3),
Stacks Tags 099I, 099L and 099M.
(auxiliary; not a blueprint node).

Proof: use pointComparison to transport the absolute-value integer coefficient ring to
its spectral-norm presentation. The normalized section-ring comparison identifies the
latter with the positive constant-quotient limit. Flat common-quotient comparison
identifies every reduction after constant scalar restriction, with its actual quotient
map. Exact section-action and small-site equivalences preserve products, shifts and
cones. On flat K-flat representatives their derived reduction comparisons identify
pure tensors and carry the quotient units and transitions to the same maps. They
therefore identify the augmented Roos triangle, including the canonical augmentation.
The quotient-tower/local-kernel completeness comparison for the principal uniformizer
ideal identifies invertibility of this augmentation with ConstantCompletion.IsComplete.
Reflection through the exact equivalences proves the reverse implication as well.
This argument applies to arbitrary unbounded K, including zero, and to empty X. -/
theorem internal_completion_stacks_comparison
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (X : Scheme.{u}) [IsNoetherian X]
    (K : DerivedCategory (AdicCompletion.Modules l E X)) :
    IsDerivedComplete l E X K ↔
      ConstantCompletion.IsComplete
        (IntegralModelsStacks.smallMap X (IntegralModelsStacks.residueMap l E X))
        (IntegralModelsStacks.smallDerivedObject X _
          ((IntegralModelsStacks.restriction l E X).obj
          ((Mod.comap (coefficientMap
            (IntegralConstantModel.pointComparison l E).inv.hom X)).mapDerivedCategory.obj
            K))) := by
  classical
  let : EssentiallySmall.{u + 1} X.ProEt := essentiallySmallSelf.{0, u, u + 1} _
  let := HasDerivedCategory.standard
    (ConstantCompletion.Mod (InternalCompletionTransport.ring l E X))
  let := HasDerivedCategory.standard
    (ℕᵒᵖ ⥤ ConstantCompletion.Mod (InternalCompletionTransport.ring l E X))
  let (U : Scheme.coefficientProEtaleSiteModel.{u, u} X) :=
    HasDerivedCategory.standard
      (ConstantCompletion.Mod ((InternalCompletionTransport.ring l E X).over U))
  have : Mono
      (ConstantCompletion.kernelIdeal (InternalCompletionTransport.residue l E X)).inclusion := by
    constructor
    intro Z f g h
    apply SheafOfModules.hom_ext
    apply PresheafOfModules.hom_ext
    intro U
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro z
    apply Subtype.ext
    exact congrArg (fun k ↦ k.val.app U z) h
  obtain ⟨a, ha⟩ := InternalCompletionTransport.residue_generator l E X
  obtain ⟨D, _, _, hD, _⟩ := ringedKoszulCompletionReflector
    (InternalCompletionTransport.ring l E X) 1 (fun _ ↦ a)
    (ConstantCompletion.kernelIdeal (InternalCompletionTransport.residue l E X)).module
    (ConstantCompletion.kernelIdeal (InternalCompletionTransport.residue l E X)).inclusion ha
  obtain ⟨P, f, hf, _, hP⟩ :=
    CochainComplex.exists_quasiIso_flat_kFlat.{u + 1, u + 2} (DerivedCategory.Q.objPreimage K)
  let := hf
  let e : DerivedCategory.Q.obj P ≅ K :=
    asIso (DerivedCategory.Q.map f) ≪≫ DerivedCategory.Q.objObjPreimageIso K
  let F := InternalCompletionTransport.functor l E X
  obtain ⟨c, hc⟩ :=
    InternalCompletionTransport.quotient_koszul_unit_comparison l E X a ha P hP D
  have hi : IsIso (DerivedCategory.Q.map (AdicCompletion.augmentation l E X P)) ↔
      IsIso (D.unit (F.obj (DerivedCategory.Q.obj P))) := by
    rw [← hc]
    constructor
    · intro h
      let := h
      infer_instance
    · intro h
      let := h
      have : IsIso (F.map (DerivedCategory.Q.map
          (AdicCompletion.augmentation l E X P))) :=
        IsIso.of_isIso_comp_right _ c.hom
      exact isIso_of_reflects_iso _ F
  have hrep : IsDerivedComplete l E X K ↔
      IsIso (DerivedCategory.Q.map (AdicCompletion.augmentation l E X P)) := by
    rw [AdicCompletion.isDerivedComplete_iff l E X K P hP e]
    change IsIso (e.inv ≫ _) ↔ _
    exact ⟨fun h ↦ by let := h; exact IsIso.of_isIso_comp_left e.inv _,
      fun h ↦ by let := h; infer_instance⟩
  exact hrep.trans (hi.trans ((hD _).trans
    ((InternalCompletionTransport.complete_iso l E X (F.mapIso e)).trans
      (InternalCompletionTransport.complete_iso l E X
        (InternalCompletionTransport.objectIso l E X K)))))

end AlgebraicGeometry.ProEtale
