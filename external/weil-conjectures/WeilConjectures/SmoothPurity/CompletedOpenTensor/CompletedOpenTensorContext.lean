/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.CompletedOpenTensor.CompletedOpenTensorRepresentativeData
import WeilConjectures.SmoothPurity.Canonical.CanonicalIntegralCompletionModels
import WeilConjectures.SmoothPurity.Normalized.NormalizedCompletionRealization
import WeilConjectures.SixFunctors.OpenSemilinearTensor.OpenSemilinearTensorModel
import all WeilConjectures.SixFunctors.IntegralOpenReduction.IntegralOpenReductionComparison
import WeilConjectures.SixFunctors.IntegralOpenReduction.NormalizedOpenSections
import WeilConjectures.SixFunctors.IntegralOpenReduction.IntegralOpenExtensionComplete
import WeilConjectures.SixFunctors.OpenRoosRestriction.OpenRoosRestrictionDescent
import WeilConjectures.DeligneLaumon.PrincipalKoszulStrictReplacement.PrincipalKoszulStrictReplacement
import all WeilConjectures.CategoryTheory.LocalizedModuleExactForSystems
import all WeilConjectures.Algebra.Homology.SmoothPurity.LocalizedModuleExactIndependent
import all WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import all Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
import all WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful

/-! # Compatible completion presentations for open extension -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall

universe c v r t u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
namespace SheafOfModules
open Classical in
private noncomputable def contextSectionIso
    {C : Type c} [Category.{v} C] {J : GrothendieckTopology C}
    (R : Sheaf J RingCat.{max c v r}) (U V : C) [Subsingleton (V ⟶ U)] (φ : V ⟶ U)
    (F : SheafOfModules.{max c v r} (R.over U)) :
    F.val.obj (op (Over.mk φ)) ≅ (extensionByZeroPresheaf R U).obj F |>.obj (op V) := by
  exact LinearEquiv.toModuleIso
    { toLinearMap := DirectSum.lof (R.obj.obj (op V)) (V ⟶ U)
        (fun ψ ↦ F.val.obj (op (Over.mk ψ))) φ
      invFun := DirectSum.component (R.obj.obj (op V)) (V ⟶ U)
        (fun ψ ↦ F.val.obj (op (Over.mk ψ))) φ
      left_inv := by
        intro x
        exact DirectSum.component.lof_self (M := fun ψ ↦ F.val.obj (op (Over.mk ψ)))
          (R.obj.obj (op V)) φ x
      right_inv := by
        intro x
        induction x using DirectSum.induction_on with
        | zero => simp
        | of ψ x =>
          have : ψ = φ := Subsingleton.elim _ _
          subst ψ
          change DirectSum.lof _ _ _ φ (DirectSum.component _ _ _ φ
            (DirectSum.lof (R.obj.obj (op V)) _
              (fun ψ ↦ F.val.obj (op (Over.mk ψ))) φ x)) = _
          rw [DirectSum.component.lof_self]
          rfl
        | add x y hx hy =>
          change DirectSum.of _ φ (x φ + y φ) = x + y
          rw [map_add]
          exact congrArg₂ (· + ·) hx hy }

open Classical in
private noncomputable def contextRestrictionIso
    {C : Type c} [Category.{v} C] {J : GrothendieckTopology C}
    (R : Sheaf J RingCat.{max c v r}) (U : C)
    (hU : ∀ V : C, Subsingleton (V ⟶ U))
    (F : SheafOfModules.{max c v r} (R.over U)) :
    ((SheafOfModules.toSheaf (R.over U)).obj F).obj ≅
      (Over.forget U).op ⋙ ((extensionByZeroPresheaf R U).obj F).presheaf := by
  refine NatIso.ofComponents (fun V ↦ ?_) ?_
  · let := hU V.unop.left
    exact (forget₂ (ModuleCat (R.obj.obj (op V.unop.left))) AddCommGrpCat).mapIso
      (contextSectionIso.{c, v, r} R U V.unop.left V.unop.hom F)
  · intro V W a
    let := hU V.unop.left
    let := hU W.unop.left
    ext x
    change _ = extensionByZeroPresheafRestrictAdd R U F
      ((Over.forget U).op.map a) (DirectSum.of _ V.unop.hom x)
    erw [extensionRestrict_of.{c, v, r} R U F ((Over.forget U).op.map a)
      V.unop.hom W.unop.hom (by exact a.unop.w)]
    rfl

private theorem contextLocalizedUnitIsIso
    {C : Type c} [Category.{v} C] {J : GrothendieckTopology C}
    [HasSheafify J AddCommGrpCat.{max c v r}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{max c v r}]
    (R : Sheaf J CommRingCat.{max c v r}) (U : C)
    (hU : ∀ V : C, Subsingleton (V ⟶ U)) :
    IsIso (localizedSystemAdjunction.{c, v, r} R U).unit := by
  let A := (sheafCompose J (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj R
  have hunit (F : SheafOfModules.{max c v r} (A.over U)) :
      IsIso ((localizedSystemAdjunction.{c, v, r} R U).unit.app F) := by
    let P := ((extensionByZeroPresheaf A U).obj F).presheaf
    let T := (Over.forget U).op ⋙ P
    have hT : Presheaf.IsSheaf (J.over U) T :=
      (Presheaf.isSheaf_of_iso_iff (contextRestrictionIso.{c, v, r} A U hU F)).mp
        ((SheafOfModules.toSheaf _).obj F).property
    have : IsIso (toSheafify (J.over U) T) := isIso_toSheafify _ hT
    have hh := (Over.forget U).toSheafify_pullbackSheafificationCompatibility
      AddCommGrpCat.{max c v r} (J.over U) J P
    have : IsIso (Functor.whiskerLeft (Over.forget U).op (toSheafify J P)) := by
      rw [← hh]
      infer_instance
    let η := (localizedSystemAdjunction.{c, v, r} R U).unit.app F
    have hη : ((SheafOfModules.toSheaf _).map η).hom =
        (contextRestrictionIso.{c, v, r} A U hU F).hom ≫
          Functor.whiskerLeft (Over.forget U).op (toSheafify J P) := by
      ext V x
      exact (localizedSystemAdjunction_existsUnique.{c, v, r} R U).exists.choose_spec F V x
    have : IsIso ((sheafToPresheaf (J.over U) AddCommGrpCat.{max c v r}).map
        ((SheafOfModules.toSheaf _).map η)) := by
      change IsIso (((SheafOfModules.toSheaf _).map η).hom)
      rw [hη]
      infer_instance
    have : IsIso ((SheafOfModules.toSheaf _).map η) :=
      isIso_of_reflects_iso _ (sheafToPresheaf (J.over U) AddCommGrpCat.{max c v r})
    exact isIso_of_reflects_iso η (SheafOfModules.toSheaf _)
  exact NatIso.isIso_of_isIso_app _
end SheafOfModules

namespace WeilConjectures.CompletedOpenTensor
open IntegralOpenReduction

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  {U V : Scheme.{t}} (j : U ⟶ V) [IsOpenImmersion j]

private theorem contextOpenUnitIsIso (o : Operations l E j) :
    IsIso (openAdjunction l E j o).unit := by
  have hW (W : V.ProEt) : Subsingleton (W ⟶ openObject j) := by
    constructor
    intro f g
    apply MorphismProperty.Over.Hom.ext
    apply (cancel_mono j).mp
    exact (MorphismProperty.Over.w f).trans (MorphismProperty.Over.w g).symm
  have : IsIso (SheafOfModules.localizedSystemAdjunction.{t + 1, t, max u (t + 1)}
      (completedIntegralCommRingSheafUnrestricted l E V) (openObject j)).unit :=
    SheafOfModules.contextLocalizedUnitIsIso.{t + 1, t, max u (t + 1)} _ _ hW
  let ff := (SheafOfModules.localizedSystemAdjunction.{t + 1, t, max u (t + 1)}
    (completedIntegralCommRingSheafUnrestricted l E V) (openObject j)).fullyFaithfulLOfIsIsoUnit
  have := ff.full
  have := ff.faithful
  have : (extension l E j o).Full := by unfold extension; infer_instance
  have : (extension l E j o).Faithful := by unfold extension; infer_instance
  have : IsIso (ordinaryAdjunction l E j o).unit :=
    (ordinaryAdjunction l E j o).unit_isIso_of_L_fully_faithful
  let a := openAdjunction l E j o
  have hQ (P : CochainComplex (scalarReductionSource l E U) ℤ) :
      IsIso (a.unit.app (DerivedCategory.Q.obj P)) := by
    have hn (n : ℤ) : IsIso
        ((((ordinaryAdjunction l E j o).mapHomologicalComplex (.up ℤ)).unit.app P).f n) :=
      inferInstanceAs (IsIso ((ordinaryAdjunction l E j o).unit.app (P.X n)))
    have := HomologicalComplex.Hom.isIso_of_components
      (((ordinaryAdjunction l E j o).mapHomologicalComplex (.up ℤ)).unit.app P)
    have he : a.unit.app (DerivedCategory.Q.obj P) =
        DerivedCategory.Q.map (((ordinaryAdjunction l E j o).mapHomologicalComplex
          (.up ℤ)).unit.app P) ≫
          (restriction l E j o).mapDerivedCategoryFactors.inv.app _ ≫
            (star l E j o).map ((extension l E j o).mapDerivedCategoryFactors.inv.app P) := by
      simp only [a, openAdjunction, SheafOfModules.OpenTensorNormalization.exactDerivedAdjunction,
        Adjunction.localization_unit_app]
      rfl
    rw [he]
    infer_instance
  have (M : DerivedCategory (scalarReductionSource l E U)) : IsIso (a.unit.app M) :=
    (NatTrans.isIso_app_iff_of_iso a.unit (DerivedCategory.Q.objObjPreimageIso M)).mp (hQ _)
  exact NatIso.isIso_of_isIso_app _

open CategoryTheory.Functor
open CanonicalOpenRestriction

private theorem comparisonOfModelSameOpen
    (hlV : IsUnit (l : Γ(V, ⊤))) (hlU : IsUnit (l : Γ(U, ⊤)))
    (SV : CoefficientDerivedSystemCalculus l E V)
    (SU : CoefficientDerivedSystemCalculus l E U)
    (o : Operations l E j) (tensor : TensorComparison l E j o)
    (AV : OpenSemilinearTensor.OrdinaryReduction l E V)
    (AU : OpenSemilinearTensor.OrdinaryReduction l E U)
    (c : OpenSemilinearTensor.Comparison l E j o SV SU AV AU tensor)
    (hext : ∀ K, complete l E U K → complete l E V ((shriek l E j o).obj K)) :
    ∃ d : Comparison l E j o SV SU tensor,
      ∀ K : (complete l E U).FullSubcategory,
        c.r.hom.app K.obj = d.r.hom.app K := by
  classical
  let hInvV (x : V) : Invertible (l : V.residueField x) :=
    (show IsUnit (l : V.residueField x) from by
      simpa only [map_natCast] using
        hlV.map ((V.presheaf.germ ⊤ x (by trivial)) ≫ V.residue x).hom).invertible
  let hInvU (x : U) : Invertible (l : U.residueField x) :=
    (show IsUnit (l : U.residueField x) from by
      simpa only [map_natCast] using
        hlU.map ((U.presheaf.germ ⊤ x (by trivial)) ≫ U.residue x).hom).invertible
  let : ∀ x : V, Invertible (l : V.residueField x) := hInvV
  let : ∀ x : U, Invertible (l : U.residueField x) := hInvU
  have hV := purNormalizedReconstruction l E V hlV SV
  have hU := purNormalizedReconstruction l E U hlU SU
  have hcall := @CanonicalOpenRestriction.canonicalOpenRestrictionModel.{t, u}
    l ‹Fact l.Prime› E ‹Field E› ‹Algebra ℚ_[l] E› ‹FiniteDimensional ℚ_[l] E›
    U V j ‹IsOpenImmersion j› o SU SV
  have hcall' := hcall c.r tensor
  obtain ⟨s, hmate, _hmodel⟩ := hcall' (by
    intro Q hQ
    obtain ⟨cU, cV, hsquare⟩ := c.model Q hQ.1 hQ.2
    refine ⟨⟨c.kflat Q hQ.1 hQ.2, c.preservesFlatTerms Q hQ.1 hQ.2⟩,
      _, _, cU.iso, cV.iso, AU.complexEvaluation l E Q,
      AV.complexEvaluation l E _,
      OpenSemilinearTensor.ordinaryChain l E j o AV AU c.ordinary Q,
      cU.presentation, cU.augmentation, cV.presentation, cV.augmentation, hsquare, ?_⟩
    intro n i
    exact c.components (Q.X i) n)
  clear hcall' hcall _hmodel
  have hc : ∀ H, complete l E V H → complete l E U ((star l E j o).obj H) :=
    fun H hH ↦ (OpenRestrictionCompleteness.openRestrictionComplete l E j o H hH).1
  have hsu (K) : SU.reduction.map ((openAdjunction l E j o).unit.app K) ≫
      s.hom.app ((shriek l E j o).obj K) ≫ (P l E j o).map (c.r.hom.app K) =
        (systemAdjunction l E j o).unit.app (SU.reduction.obj K) := by
    rw [hmate, ← Category.assoc]
    rw [show SU.reduction.map ((openAdjunction l E j o).unit.app K) ≫
        ((mateEquiv (openAdjunction l E j o) (systemAdjunction l E j o)
          (TwoSquare.mk _ _ _ _ c.r.inv)).app ((shriek l E j o).obj K)) =
        (systemAdjunction l E j o).unit.app (SU.reduction.obj K) ≫
          (P l E j o).map (c.r.inv.app K) from
      unit_mateEquiv (openAdjunction l E j o) (systemAdjunction l E j o)
        (TwoSquare.mk _ _ _ _ c.r.inv) K]
    simp [← Functor.map_comp]
  have hsc (H) : SV.reduction.map ((openAdjunction l E j o).counit.app H) =
      c.r.hom.app ((star l E j o).obj H) ≫ (J l E j o).map (s.hom.app H) ≫
        (systemAdjunction l E j o).counit.app (SV.reduction.obj H) := by
    rw [hmate]
    rw [show (J l E j o).map
        ((mateEquiv (openAdjunction l E j o) (systemAdjunction l E j o)
          (TwoSquare.mk _ _ _ _ c.r.inv)).app H) ≫
        (systemAdjunction l E j o).counit.app (SV.reduction.obj H) =
        c.r.inv.app ((star l E j o).obj H) ≫
          SV.reduction.map ((openAdjunction l E j o).counit.app H) from
      mateEquiv_counit (openAdjunction l E j o) (systemAdjunction l E j o)
        (TwoSquare.mk _ _ _ _ c.r.inv) H]
    simp
  let di := inverseUnitIso SV.adjunction
    ((complete l E U).ι ⋙ shriek l E j o)
    ((complete l E U).ι ⋙ SU.reduction ⋙ J l E j o)
    (isoWhiskerLeft (complete l E U).ι c.r)
    (fun K ↦ hV.2 _ (hext _ K.property))
  let bi := inverseUnitIso SU.adjunction
    ((complete l E V).ι ⋙ star l E j o)
    ((complete l E V).ι ⋙ SV.reduction ⋙ P l E j o)
    (isoWhiskerLeft (complete l E V).ι s)
    (fun H ↦ hU.2 _ (hc _ H.property))
  let uU (K : (complete l E U).FullSubcategory) :=
    @asIso _ _ _ _ (SU.adjunction.unit.app K.obj) (hU.2 _ K.property)
  let uV (H : (complete l E V).FullSubcategory) :=
    @asIso _ _ _ _ (SV.adjunction.unit.app H.obj) (hV.2 _ H.property)
  refine ⟨{
    r := isoWhiskerLeft (complete l E U).ι c.r
    extensionComplete := fun K ↦ hext K.obj K.property
    restrictionComplete := fun H ↦ hc H.obj H.property
    s := isoWhiskerLeft (complete l E V).ι s
    unitU := uU
    unitUHom := fun _ ↦ rfl
    unitX := uV
    unitXHom := fun _ ↦ rfl
    d := di
    dFormula := fun _ ↦ rfl
    reductionD := fun K ↦ inverseUnitIso_normalization SV.adjunction _ _ _ _ K
    pullRealization := bi
    pullFormula := fun _ ↦ rfl
    systemUnit := fun K ↦ hsu K.obj
    systemCounit := fun H ↦ (hsc H.obj).symm
    realizedUnit := ?_
    realizedCounit := ?_
    strictModel := ?_ }, fun _ ↦ rfl⟩
  · intro K
    let : IsIso (SU.adjunction.unit.app
        ((star l E j o).obj ((shriek l E j o).obj K.obj))) :=
      hU.2 _ (hc _ (hext _ K.property))
    have ht : (systemAdjunction l E j o).unit.app (SU.reduction.obj K.obj) ≫
        (P l E j o).map (c.r.inv.app K.obj) ≫
        s.inv.app ((shriek l E j o).obj K.obj) =
        SU.reduction.map ((openAdjunction l E j o).unit.app K.obj) := by
      rw [← hsu K.obj]
      simp only [Category.assoc, ← Functor.map_comp_assoc, Iso.hom_inv_id_app]
      erw [(P l E j o).map_id]
      simp only [Category.id_comp, Iso.hom_inv_id_app]
      erw [Category.comp_id]
    dsimp only [bi, inverseUnitIso, NatIso.ofComponents_hom_app, Iso.trans_hom,
      Iso.symm_hom, Functor.mapIso_hom, asIso_inv, Iso.app_hom, uU, asIso_hom,
      isoWhiskerLeft_inv, whiskerLeft_app, Functor.comp_obj, ObjectProperty.ι_obj]
    simp only [← Functor.map_comp_assoc]
    rw [ht]
    exact @inverse_unit_natural _ _ _ _ _ _ SU.adjunction K.obj
      ((star l E j o).obj ((shriek l E j o).obj K.obj))
      ((openAdjunction l E j o).unit.app K.obj)
      (hU.2 _ (hc _ (hext _ K.property)))
  · intro H
    dsimp only [di, inverseUnitIso, NatIso.ofComponents_inv_app, Iso.trans_inv,
      Iso.symm_inv, Functor.mapIso_inv, asIso_hom, Iso.app_inv, uV, asIso_inv,
      isoWhiskerLeft_hom, whiskerLeft_app, Functor.comp_obj]
    exact @realize_counit_composite _ _ _ _ _ _ SV.adjunction _ H.obj _ _
      ((openAdjunction l E j o).counit.app H.obj)
      (c.r.hom.app ((star l E j o).obj H.obj))
      ((J l E j o).map (s.hom.app H.obj))
      ((systemAdjunction l E j o).counit.app (SV.reduction.obj H.obj))
      (hsc H.obj).symm (hV.2 H.obj H.property)
  · intro Q hQ hf hcomplete
    obtain ⟨cU, cV, hsquare⟩ := c.model Q hQ hf
    refine ⟨c.kflat Q hQ hf, _, _, cU.iso, cV.iso,
      AU.complexEvaluation l E Q, AV.complexEvaluation l E _,
      OpenSemilinearTensor.ordinaryChain l E j o AV AU c.ordinary Q,
      cU.presentation, cU.augmentation, cV.presentation, cV.augmentation, hsquare, ?_⟩
    intro n i
    exact c.components (Q.X i) n

/-- Compatible presentations of reduction, completion and the strict open comparison.
Source: Stacks Tags 0GL1, 0E8I, 0941 and 099B; step 1 of
lem-pur-completed-open-tensor-representatives.
(blueprint: lem-pur-completed-open-tensor-context).

Proof: use CompletionUnit.canonicalModels to choose coherent reduction/limit calculi
and ordinary and derived models on U and V, with independent universes. Compare their
integral closed structures with the canonical IntegralOnSlice.duality structures by
the total-tensor representative comparison and tensor-Hom transposition. Replace
the integral closed fields by the canonical structures and conjugate their tensor,
evaluation and currying comparisons by those isomorphisms. Keep the reduction functors
and their adjunctions. The coherence equations are transported by naturality and
cancellation of these isomorphisms, giving tensorV and tensorU as equalities.

Use the scalar-normalized slice coefficient isomorphisms and the ordinary quotient
reductions to construct one set of exact open operations and their semilinear model.
Its all-input comparison is the localization of the ordinary quotient-system chain
comparison. Restrict that same map to complete inputs for completeOpen.r. Construct
completeOpen.d by applying total limit to its inverse and then the inverse actual
reduction/limit unit. integralOpenExtensionComplete and normalized reconstruction
make that unit invertible;
the comparison's unit and realization equations follow from the adjunction triangles.

For completionV/U, apply normalizedCompletionRealization to compare the published
quotient/Roos completion with reduction
followed by total limit on flat-term K-flat representatives. Both are computed by
the same quotient tower. Their strict augmentations have the recorded
coefficientIntegralScalarUnitSection components, so the comparison identifies
completionUnit with the actual reduction/limit adjunction unit. Descent from the
good-complex localization gives
completionV/U and the required unitV/U equations on every derived input.

Restriction to an open is exact and has an exact extension-by-zero left adjoint,
so it preserves the products computing the Roos total limit. The scalar-normalized
slice coefficient isomorphisms identify its termwise quotient towers. Commuting
restriction with the two Roos coordinates gives restrictionCompletion, as in
OpenRoosRestriction.restrictionDescent. Equality
of the strict augmentations gives restrictionUnit after localization. Finally, the
slice insertion/collapse pair is the actual ordinary open adjunction unit and is
invertible for the subterminal open object. Its localization gives openUnit and
openUnitHom for the very same operations. Thus the Context fields are compatible
presentations of fixed maps, rather than independently chosen comparison witnesses.
Empty and identity opens use the same constructions. This step constructs no ordinary
tensor comparison and asserts none of its representative squares. -/
theorem completedOpenTensorContext [QuasiCompact j]
    (hlV : IsUnit (l : Γ(V, ⊤))) (hlU : IsUnit (l : Γ(U, ⊤))) :
    Nonempty (Context l E j) := by
  classical
  obtain ⟨SV, cV, OV, ⟨DV⟩, hV⟩ := canonicalIntegralCompletionModels l E V hlV
  obtain ⟨SU, cU, OU, ⟨DU⟩, hU⟩ := canonicalIntegralCompletionModels l E U hlU
  obtain ⟨sections, hsections⟩ := normalizedOpenSections l E j
  obtain ⟨o, AV, AU, tc, _ho, ⟨strict⟩⟩ :=
    OpenSemilinearTensor.openSemilinearTensorModel l E j hlV hlU SV SU cV cU
      sections hsections
  obtain ⟨completeOpen, sameOpen⟩ := comparisonOfModelSameOpen l E j hlV hlU SV SU o tc
    AV AU strict (integralOpenExtensionComplete l E j hlV hlU o)
  have hv (x : V) : IsUnit (l : V.presheaf.stalk x) := by
    simpa only [map_natCast] using hlV.map (V.presheaf.germ ⊤ x (by trivial)).hom
  have hu (x : U) : IsUnit (l : U.presheaf.stalk x) := by
    simpa only [map_natCast] using hlU.map (U.presheaf.germ ⊤ x (by trivial)).hom
  obtain ⟨completionV, unitV⟩ := normalizedCompletionRealization l E V SV OV DV hv
  obtain ⟨completionU, unitU⟩ := normalizedCompletionRealization l E U SU OU DU hu
  obtain ⟨d, hd, _⟩ := PrincipalKoszulStrictReplacement.coefficient_datum l E
  obtain ⟨_, _, _, rho, _c, hrho, _⟩ :=
    OpenRoosRestriction.restrictionDescent l E j o d hd
  have hi : IsIso (openAdjunction l E j o).unit := contextOpenUnitIsIso l E j o
  exact ⟨{
    ambient := SV
    openSite := SU
    ambientCoherence := cV
    openCoherence := cU
    operations := o
    coefficients := tc
    completeOpen := completeOpen
    ordinaryV := AV
    ordinaryU := AU
    strictOpen := strict
    sameOpen := sameOpen
    tensorV := hV
    tensorU := hU
    completionV := completionV
    completionU := completionU
    unitV := unitV
    unitU := unitU
    openUnit := asIso (openAdjunction l E j o).unit
    openUnitHom := rfl
    restrictionCompletion := rho
    restrictionUnit := hrho }⟩

end WeilConjectures.CompletedOpenTensor
