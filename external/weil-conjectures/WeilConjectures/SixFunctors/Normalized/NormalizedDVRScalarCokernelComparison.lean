/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.Normalized.NormalizedDVRTower
public import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
public import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
public import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
public import Mathlib.CategoryTheory.Limits.EssentiallySmall
public import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
public import WeilConjectures.DeligneLaumon.PrincipalKoszulStrictReplacement.PrincipalKoszulStrictReplacement
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.HomModule
import WeilConjectures.Algebra.Homology.System.SystemScalarModel
import Mathlib.Algebra.Module.Hom
import Mathlib.CategoryTheory.Yoneda
import all WeilConjectures.DeligneLaumon.PrincipalKoszulStrictReplacement.PrincipalKoszulStrictReplacement
import all WeilConjectures.AlgebraicGeometry.Completed.CompletedIntegralFiniteQuotientHomExt

/-! # Scalar cokernels of universal finite-coefficient chain maps

Source: Stacks Tags 03EK, 06YS and 06YY; blueprint DVR effectivity,
coefficient quotient step. (blueprint: lem-coef-normalized-dvr-scalar-cokernel-comparison).
-/

@[expose] public noncomputable section
set_option autoImplicit false
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
universe d t u
open CategoryTheory CategoryTheory.Limits Opposite
@[instance_reducible] private noncomputable def descendedAction
    {A B : Type*} [Ring A] [Ring B] (p : A →+* B) (hp : Function.Surjective p)
    (M : Type*) [AddCommGroup M] [Module A M]
    (hk : ∀ a, p a = 0 → ∀ x : M, a • x = 0) : Module B M :=
  Module.compHom M (p.liftOfSurjective hp ⟨Module.toAddMonoidEnd A M, by
    intro a ha
    ext x
    exact hk a ha x⟩)

private lemma descendedAction_smul
    {A B : Type*} [Ring A] [Ring B] (p : A →+* B) (hp : Function.Surjective p)
    (M : Type*) [AddCommGroup M] [Module A M]
    (hk : ∀ a, p a = 0 → ∀ x : M, a • x = 0) (a : A) (x : M) :
    let := descendedAction p hp M hk
    p a • x = a • x := by
  have hker : RingHom.ker p ≤ RingHom.ker (Module.toAddMonoidEnd A M) := by
    intro b hb
    ext y
    exact hk b hb y
  change (p.liftOfSurjective hp ⟨Module.toAddMonoidEnd A M, hker⟩ (p a)) x = _
  rw [RingHom.liftOfSurjective_comp_apply]
  rfl

private noncomputable def descendedSheaf
    {C : Type*} [Category* C] {J : GrothendieckTopology C}
    {R S : Sheaf J RingCat.{u}} (p : R ⟶ S)
    (hp : ∀ U, Function.Surjective (p.hom.app U)) (M : SheafOfModules.{u} R)
    (hk : ∀ U a, p.hom.app U a = 0 → ∀ x : M.val.obj U, a • x = 0) :
    SheafOfModules.{u} S where
  val :=
    { obj U := by
        let := descendedAction (p.hom.app U).hom (hp U) (M.val.obj U) (hk U)
        exact ModuleCat.of (S.obj.obj U) (M.val.obj U)
      map {U V} f := by
        let := descendedAction (p.hom.app U).hom (hp U) (M.val.obj U) (hk U)
        let := descendedAction (p.hom.app V).hom (hp V) (M.val.obj V) (hk V)
        let MU := ModuleCat.of (S.obj.obj U) (M.val.obj U)
        let MV := ModuleCat.of (S.obj.obj V) (M.val.obj V)
        exact ModuleCat.ofHom (X := MU)
          (Y := (ModuleCat.restrictScalars (S.obj.map f).hom).obj MV)
          { toFun := fun x ↦ M.val.map f x
            map_add' := map_add _
            map_smul' := by
              intro b x
              obtain ⟨a, rfl⟩ := hp U b
              change (show M.val.obj V from M.val.map f (p.hom.app U a • x)) =
                S.obj.map f (p.hom.app U a) • (show M.val.obj V from M.val.map f x)
              rw [descendedAction_smul]
              have hn := congrArg (fun k ↦ k a) (p.hom.naturality f)
              change p.hom.app V (R.obj.map f a) = S.obj.map f (p.hom.app U a) at hn
              rw [← hn, descendedAction_smul]
              exact M.val.map_smul f a x }
      map_id U := by ext x; exact congrArg (fun k ↦ k x) (M.val.map_id U)
      map_comp f g := by ext x; exact M.val.map_comp_apply f g x }
  isSheaf := by exact M.isSheaf

private noncomputable def descendedSheafIso
    {C : Type*} [Category* C] {J : GrothendieckTopology C}
    {R S : Sheaf J RingCat.{u}} (p : R ⟶ S)
    (hp : ∀ U, Function.Surjective (p.hom.app U)) (M : SheafOfModules.{u} R)
    (hk : ∀ U a, p.hom.app U a = 0 → ∀ x : M.val.obj U, a • x = 0) :
    (SheafOfModules.restrictScalars p).obj (descendedSheaf p hp M hk) ≅ M := by
  let e U : ((SheafOfModules.restrictScalars p).obj
      (descendedSheaf p hp M hk)).val.obj U ≅ M.val.obj U :=
    { hom := ModuleCat.ofHom (X := ((SheafOfModules.restrictScalars p).obj
        (descendedSheaf p hp M hk)).val.obj U) (Y := M.val.obj U)
        { toFun := fun x ↦ x
          map_add' := fun _ _ ↦ rfl
          map_smul' := fun a x ↦ descendedAction_smul (p.hom.app U).hom (hp U) _ (hk U) a x }
      inv := ModuleCat.ofHom (X := M.val.obj U)
        (Y := ((SheafOfModules.restrictScalars p).obj (descendedSheaf p hp M hk)).val.obj U)
        { toFun := fun x ↦ x
          map_add' := fun _ _ ↦ rfl
          map_smul' := fun a x ↦ (descendedAction_smul
            (p.hom.app U).hom (hp U) _ (hk U) a x).symm } }
  exact (SheafOfModules.fullyFaithfulForget R).preimageIso
    (PresheafOfModules.isoMk e (by intro U V f; ext x; rfl))

private theorem restriction_full
    {C : Type*} [Category* C] {J : GrothendieckTopology C}
    {R S : Sheaf J RingCat.{u}} (p : R ⟶ S)
    (hp : ∀ U, Function.Surjective (p.hom.app U)) :
    (SheafOfModules.restrictScalars.{u} p).Full where
  map_surjective {M N} f := by
    let g : M ⟶ N :=
      { val :=
          { app U := ModuleCat.ofHom
              { toFun := f.val.app U
                map_add' := map_add _
                map_smul' := by
                  intro b x
                  obtain ⟨a, rfl⟩ := hp U b
                  exact (f.val.app U).hom.map_smul a x }
            naturality := by
              intro U V k
              ext x
              exact PresheafOfModules.naturality_apply f.val k x } }
    exact ⟨g, rfl⟩

private theorem restriction_faithful
    {C : Type*} [Category* C] {J : GrothendieckTopology C}
    {R S : Sheaf J RingCat.{u}} (p : R ⟶ S) :
    (SheafOfModules.restrictScalars.{u} p).Faithful where
  map_injective {M N} f g h := by
    ext U x
    exact congrArg (fun k ↦ k.val.app U x) h

private theorem complex_in_restriction_image
    {C : Type*} [Category* C] {J : GrothendieckTopology C}
    {R S : Sheaf J RingCat.{u}} (p : R ⟶ S)
    (hp : ∀ U, Function.Surjective (p.hom.app U))
    (K : CochainComplex (SheafOfModules.{u} R) ℤ)
    (hk : ∀ i U a, p.hom.app U a = 0 → ∀ x : (K.X i).val.obj U, a • x = 0) :
    ∃ L : CochainComplex (SheafOfModules.{u} S) ℤ,
      Nonempty (((SheafOfModules.restrictScalars p).mapHomologicalComplex (.up ℤ)).obj L ≅ K) := by
  let T := SheafOfModules.restrictScalars.{u} p
  let : T.Full := restriction_full p hp
  let : T.Faithful := restriction_faithful p
  let M i := descendedSheaf p hp (K.X i) (hk i)
  let e i : T.obj (M i) ≅ K.X i := descendedSheafIso p hp (K.X i) (hk i)
  let L : CochainComplex (SheafOfModules.{u} S) ℤ :=
    { X := M
      d i j := T.preimage ((e i).hom ≫ K.d i j ≫ (e j).inv)
      shape i j h := by
        apply T.map_injective
        simp [K.shape i j h]
      d_comp_d' i j k _ _ := by
        apply T.map_injective
        simp }
  refine ⟨L, ⟨HomologicalComplex.Hom.isoOfComponents e ?_⟩⟩
  intro i j _
  change (e i).hom ≫ K.d i j =
    T.map (T.preimage ((e i).hom ≫ K.d i j ≫ (e j).inv)) ≫ (e j).hom
  simp only [Functor.map_preimage, Category.assoc, Iso.inv_hom_id, Category.comp_id]

-- A cokernel in the larger category, lying in the image of the right adjoint,
-- identifies the adjunction unit with that cokernel.
private theorem unit_cokernel
    {A B C : Type*} [Category A] [Category B] [Category C]
    [HasZeroMorphisms C]
    (R : B ⥤ A) (S : A ⥤ C) [S.Full] [S.Faithful]
    [R.Faithful] [R.Full] (L : A ⥤ B) (adj : L ⊣ R)
    (P : A) (v : S.obj P ⟶ S.obj P) [HasCokernel v]
    (hz : v ≫ S.map (adj.unit.app P) = 0)
    (himage : ∃ N : B, Nonempty (S.obj (R.obj N) ≅ cokernel v)) :
    IsIso (cokernel.desc v (S.map (adj.unit.app P)) hz) := by
  classical
  obtain ⟨N, ⟨e⟩⟩ := himage
  let q : P ⟶ R.obj N := S.preimage (cokernel.π v ≫ e.inv)
  let g : L.obj P ⟶ N := (adj.homEquiv P N).symm q
  have hg : adj.unit.app P ≫ R.map g = q :=
    (adj.homEquiv P N).apply_symm_apply q
  let d := cokernel.desc v (S.map (adj.unit.app P)) hz
  have hd : cokernel.π v ≫ d = S.map (adj.unit.app P) := cokernel.π_desc _ _ _
  have hfac : S.map (adj.unit.app P) ≫ S.map (R.map g) ≫ e.hom = cokernel.π v := by
    rw [← S.map_comp_assoc, hg, Functor.map_preimage]
    simp
  have hgiso : IsIso g := by
    apply isIso_of_coyoneda_map_bijective
    intro Z
    have hq : Function.Bijective (fun b : N ⟶ Z ↦ q ≫ R.map b) := by
      constructor
      · intro b c h
        apply R.map_injective
        apply S.map_injective
        apply (cancel_epi e.inv).1
        apply (cancel_epi (cokernel.π v)).1
        have hh := congrArg S.map h
        simpa only [Functor.map_comp, q, Functor.map_preimage, Category.assoc] using hh
      · intro b
        have hb : v ≫ S.map b = 0 := by
          -- Every map into R(Z) is the adjoint of a map out of L(P).
          obtain ⟨b', rfl⟩ := (adj.homEquiv P Z).surjective b
          rw [Adjunction.homEquiv_unit, Functor.map_comp, ← Category.assoc, hz, zero_comp]
        let a := S.preimage (e.hom ≫ cokernel.desc v (S.map b) hb)
        refine ⟨R.preimage a, ?_⟩
        apply S.map_injective
        simp [q, a, Category.assoc]
    have heq : (fun b : N ⟶ Z ↦ q ≫ R.map b) =
        (fun b : L.obj P ⟶ Z ↦ adj.homEquiv P Z b) ∘ (fun b : N ⟶ Z ↦ g ≫ b) := by
      funext b
      simp only [Function.comp_apply, Adjunction.homEquiv_unit, Functor.map_comp,
        ← Category.assoc, hg]
    rw [heq] at hq
    exact hq.of_comp_left (adj.homEquiv P Z).injective
  have heq : d ≫ S.map (R.map g) ≫ e.hom = 𝟙 _ := by
    apply (cancel_epi (cokernel.π v)).1
    simpa only [← Category.assoc, hd, Category.comp_id] using hfac
  have : IsIso (S.map (R.map g) ≫ e.hom) := by infer_instance
  have hd' : d = inv (S.map (R.map g) ≫ e.hom) := by
    apply (cancel_mono (S.map (R.map g) ≫ e.hom)).1
    simpa using heq
  change IsIso d
  rw [hd']
  infer_instance

namespace WeilConjectures

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (X : AlgebraicGeometry.Scheme.{t})
  (D : FiniteFieldDatum.{d}) (hl : l ≠ D.p)

local instance (priority := 10000) instNormalizedDVRScalarCokernelComparison1
    : EssentiallySmall.{max u (t + 1)} X.ProEt :=
  essentiallySmallSelf.{u} X.ProEt
local instance (priority := 10000) instNormalizedDVRScalarCokernelComparison2
    : HasSheafify (AlgebraicGeometry.Scheme.ProEt.topology X)
    AddCommGrpCat.{max u (t + 1)} := integralCoefficientAbSheafify.{t, u} X
local instance (priority := 10000) instNormalizedDVRScalarCokernelComparison3 :
    (AlgebraicGeometry.Scheme.ProEt.topology X).WEqualsLocallyBijective
      AddCommGrpCat.{max u (t + 1)} := integralCoefficientAbLocallyBijective.{t, u} X
local instance instNormalizedDVRScalarCokernelComparison4
    : HasDerivedCategory (completedIntegralModuleSheaves l E X D hl) :=
  HasDerivedCategory.standard _
local instance instNormalizedDVRScalarCokernelComparison5
    (j : ℕ) : HasDerivedCategory (normalizedDVRModules l E X j) :=
  HasDerivedCategory.standard _
local instance instNormalizedDVRScalarCokernelComparison6 (j : ℕ) :
    (completedIntegralRestrictScalars l E X D hl j).PreservesZeroMorphisms :=
  inferInstanceAs (SheafOfModules.restrictScalars.{max u (t + 1)}
    (completedIntegralCoefficientProjection l E X D hl j)).PreservesZeroMorphisms
local instance instNormalizedDVRScalarCokernelComparison7 (j : ℕ) :
    (completedIntegralRestrictScalars l E X D hl j).Additive :=
  inferInstanceAs (SheafOfModules.restrictScalars.{max u (t + 1)}
    (completedIntegralCoefficientProjection l E X D hl j)).Additive
local instance instNormalizedDVRScalarCokernelComparison8 :
    Linear (RingCat.sectionsSubring
      ((completedIntegralCommRingSheafUnrestricted l E X).obj ⋙ forget₂ CommRingCat RingCat))
      (completedIntegralModuleSheaves l E X D hl) :=
  SheafOfModules.homLinear (completedIntegralCommRingSheafUnrestricted l E X).obj
    (completedIntegralCoefficientSheafUnrestricted l E X).property

private abbrev scalarSection :
    RingCat.sectionsSubring
      ((completedIntegralCommRingSheafUnrestricted l E X).obj ⋙ forget₂ CommRingCat RingCat) :=
  ⟨(PrincipalKoszulStrictReplacement.uniformizer l E X).val,
    (PrincipalKoszulStrictReplacement.uniformizer l E X).property⟩

private theorem projection_surjective (n : ℕ) (U : X.ProEtᵒᵖ) :
    Function.Surjective ((completedIntegralCoefficientProjection l E X D hl n).hom.app U) := by
  intro x
  obtain ⟨y, hy⟩ := AlgebraicGeometry.ProEtale.constantQuotient_surjective l E X n U x
  refine ⟨(integralConstantToCompletionOfUniverses l E X).hom.app U y, ?_⟩
  exact (congrArg (fun k ↦ k.hom.app U y)
    (limit.lift_π (integralConstantConeOfUniverses l E X) (op n))).trans hy

private theorem scalar_zero (n : ℕ)
    (K : CochainComplex (normalizedDVRModules l E X n) ℤ) :
    scalarSection l E X ^ (n + 1) •
      𝟙 (((completedIntegralRestrictScalars l E X D hl n).mapHomologicalComplex
        (.up ℤ)).obj K) = 0 := by
  ext j U x
  change (limit.π (integralCoefficientSheafSystem l E X) (op n)).hom.app U
    (PrincipalKoszulStrictReplacement.scalar l E X U ^ (n + 1)) •
      (show (K.X j).val.obj U from x) = 0
  rw [PrincipalKoszulStrictReplacement.scalar_projection_zero]
  exact zero_smul ((integralCoefficientSheaf l E X n).obj.obj U)
    (show (K.X j).val.obj U from x)

private def finiteQuotientComm {m n : ℕ} (h : n ≤ m) :
    integralCoefficientCommRingSheaf l E X m ⟶ integralCoefficientCommRingSheaf l E X n where
  hom :=
    { app U := CommRingCat.ofHom ((normalizedDVRQuotient l E X h).hom.app U).hom
      naturality := by
        intro U V f
        apply (forget₂ CommRingCat RingCat).map_injective
        exact (normalizedDVRQuotient l E X h).hom.naturality f }

private theorem ordinary_transpose_quasiIso
    {m n : ℕ} (h : n ≤ m)
    (S : SheafOfModules.SystemScalarModel.{t + 1, t, max u (t + 1)} (finiteQuotientComm l E X h))
    (F : CochainComplex (normalizedDVRModules l E X m) ℤ)
    (K : CochainComplex (normalizedDVRModules l E X n) ℤ)
    (f : F ⟶ ((normalizedDVRModuleRes l E X h).mapHomologicalComplex (.up ℤ)).obj K)
    (hF : CochainComplex.IsKFlatIndependentCoefficients F)
    (hf : ∀ Z : normalizedDVRDerived l E X n,
      Function.Bijective (fun b : DerivedCategory.Q.obj K ⟶ Z ↦
        (DerivedCategory.Q.map f ≫
          (normalizedDVRModuleRes l E X h).mapDerivedCategoryFactors.inv.app K) ≫
          (normalizedDVRRes l E X h).map b)) :
    QuasiIso ((S.ordinaryAdj.mapHomologicalComplex (.up ℤ)).homEquiv F K |>.symm f) := by
  let a := S.ordinaryAdj.mapHomologicalComplex (.up ℤ)
  let g := (a.homEquiv F K).symm f
  let qf := DerivedCategory.Q.map f ≫
    (normalizedDVRModuleRes l E X h).mapDerivedCategoryFactors.inv.app K
  let d := (S.adjunction.homEquiv (DerivedCategory.Q.obj F)
    (DerivedCategory.Q.obj K)).symm qf
  have hd : IsIso d := by
    apply isIso_of_coyoneda_map_bijective
    intro Z
    have he : (fun b : (DerivedCategory.Q (C := normalizedDVRModules l E X n)).obj K ⟶ Z ↦
        qf ≫ (normalizedDVRRes l E X h).map b) =
        (fun b ↦ S.adjunction.homEquiv (DerivedCategory.Q.obj F) Z b) ∘
          (fun b : (DerivedCategory.Q (C := normalizedDVRModules l E X n)).obj K ⟶ Z ↦ d ≫ b) := by
      funext b
      dsimp only [Function.comp_apply]
      rw [Adjunction.homEquiv_naturality_right]
      simp only [d, Equiv.apply_symm_apply]
      rfl
    have hb := hf Z
    change Function.Bijective (fun b :
      (DerivedCategory.Q (C := normalizedDVRModules l E X n)).obj K ⟶ Z ↦
      qf ≫ (normalizedDVRRes l E X h).map b) at hb
    rw [he] at hb
    exact hb.of_comp_left (S.adjunction.homEquiv _ _).injective
  have ht : S.model.ε.app F ≫ DerivedCategory.Q.map g = d := by
    apply (S.adjunction.homEquiv _ _).injective
    rw [S.transpose]
    simp only [g, a, Equiv.apply_symm_apply, d, qf]
    rfl
  have := S.model.computes F hF
  have hqg : IsIso (DerivedCategory.Q.map g) := by
    have : IsIso (S.model.ε.app F ≫ DerivedCategory.Q.map g) := ht.symm ▸ hd
    exact IsIso.of_isIso_comp_left (S.model.ε.app F) (DerivedCategory.Q.map g)
  exact (DerivedCategory.isIso_Q_map_iff_quasiIso _ g).1 hqg

/-- A universal derived extension map from a K-flat finite-coefficient complex
induces a quasi-isomorphism from its scalar cokernel after exact completed restriction.
This is the coefficient calculation only: there is no tower, representative family,
successor composition, normalization datum, or inserted zero level.

Source: Stacks Tags 03EK, 06YS and 06YY; blueprint DVR effectivity, strict-model
coefficient quotient step. (blueprint: lem-coef-normalized-dvr-scalar-cokernel-comparison).

Proof: The finite quotient has kernel generated by the indicated uniformizer power.
Ordinary extension of scalars is the cokernel of multiplication by this power: the
extension unit kills it, and tensor balance gives the unique factor of every linear
map killing it. This is a right exact presentation and needs no flatness. Apply this
presentation in every degree of F. The ordinary extension computes derived extension
because F is K-flat. The displayed Hom bijections identify the adjoint of f with an
isomorphism by uniqueness of universal arrows. Consequently the ordinary adjoint of
f is a quasi-isomorphism. Exact completed restriction preserves the cokernel and this
quasi-isomorphism. Its composition with the restriction comparison i is the displayed
cokernel descent, by the adjunction unit identity. Every choice of i differs by an
isomorphism, so the conclusion is independent of this comparison. The argument includes
equal indices, zero modules, unbounded complexes, and the empty scheme. -/
theorem normalizedDVR_scalar_cokernel_comparison
    {m n : ℕ} (h : n ≤ m)
    (i : normalizedDVRModuleRes l E X h ⋙ completedIntegralRestrictScalars l E X D hl m ≅
      completedIntegralRestrictScalars l E X D hl n)
    (F : CochainComplex (normalizedDVRModules l E X m) ℤ)
    (K : CochainComplex (normalizedDVRModules l E X n) ℤ)
    (f : F ⟶ ((normalizedDVRModuleRes l E X h).mapHomologicalComplex (.up ℤ)).obj K)
    (hF : CochainComplex.IsKFlatIndependentCoefficients F)
    (hf : ∀ Z : normalizedDVRDerived l E X n,
      Function.Bijective (fun b : DerivedCategory.Q.obj K ⟶ Z ↦
        (DerivedCategory.Q.map f ≫
          (normalizedDVRModuleRes l E X h).mapDerivedCategoryFactors.inv.app K) ≫
          (normalizedDVRRes l E X h).map b))
    (hz : ((⟨(PrincipalKoszulStrictReplacement.uniformizer l E X).val,
        (PrincipalKoszulStrictReplacement.uniformizer l E X).property⟩ :
      RingCat.sectionsSubring ((completedIntegralCommRingSheafUnrestricted l E X).obj ⋙
        forget₂ CommRingCat RingCat)) ^ (n + 1) •
        𝟙 (((completedIntegralRestrictScalars l E X D hl m).mapHomologicalComplex
          (.up ℤ)).obj F)) ≫
      (((completedIntegralRestrictScalars l E X D hl m).mapHomologicalComplex
        (.up ℤ)).map f ≫ (Functor.mapHomologicalComplexCompIso
          i (.up ℤ)).hom.app K) = 0) :
    QuasiIso (cokernel.desc ((⟨(PrincipalKoszulStrictReplacement.uniformizer l E X).val,
        (PrincipalKoszulStrictReplacement.uniformizer l E X).property⟩ :
      RingCat.sectionsSubring ((completedIntegralCommRingSheafUnrestricted l E X).obj ⋙
        forget₂ CommRingCat RingCat)) ^ (n + 1) •
        𝟙 (((completedIntegralRestrictScalars l E X D hl m).mapHomologicalComplex
          (.up ℤ)).obj F))
      (((completedIntegralRestrictScalars l E X D hl m).mapHomologicalComplex
        (.up ℤ)).map f ≫ (Functor.mapHomologicalComplexCompIso
          i (.up ℤ)).hom.app K) hz) := by
  classical
  let R := normalizedDVRModuleRes l E X h
  let Sm := completedIntegralRestrictScalars l E X D hl m
  let Sn := completedIntegralRestrictScalars l E X D hl n
  let RC := R.mapHomologicalComplex (.up ℤ)
  let SC := Sm.mapHomologicalComplex (.up ℤ)
  let NC := Sn.mapHomologicalComplex (.up ℤ)
  let iC : RC ⋙ SC ≅ NC := Functor.mapHomologicalComplexCompIso i (.up ℤ)
  let r := scalarSection l E X ^ (n + 1)
  let v := r • 𝟙 (SC.obj F)
  have hp (j : ℕ) := projection_surjective l E X D hl j
  have hpq (U : X.ProEtᵒᵖ) :
      Function.Surjective ((normalizedDVRQuotient l E X h).hom.app U) := by
    intro b
    obtain ⟨a, ha⟩ := hp n U b
    refine ⟨(completedIntegralCoefficientProjection l E X D hl m).hom.app U a, ?_⟩
    exact (congrArg (fun k ↦ k.hom.app U a)
      (limit.w (integralCoefficientSheafSystem l E X) (homOfLE h).op)).trans ha
  let : R.Full := restriction_full (normalizedDVRQuotient l E X h) hpq
  let : R.Faithful := restriction_faithful (normalizedDVRQuotient l E X h)
  let : Sm.Full := restriction_full
    (completedIntegralCoefficientProjection l E X D hl m) (hp m)
  let : Sm.Faithful := restriction_faithful
    (completedIntegralCoefficientProjection l E X D hl m)
  obtain ⟨S⟩ := SheafOfModules.nonempty_systemScalarModel (finiteQuotientComm l E X h)
  let EC := S.model.E.mapHomologicalComplex (.up ℤ)
  let adj : EC ⊣ RC := S.ordinaryAdj.mapHomologicalComplex (.up ℤ)
  let g : EC.obj F ⟶ K := (adj.homEquiv F K).symm f
  have hg : QuasiIso g := ordinary_transpose_quasiIso l E X h S F K f hF hf
  have hscalar : r • 𝟙 (cokernel v) = 0 := by
    apply (cancel_epi (cokernel.π v)).1
    simpa only [Linear.comp_smul, Category.comp_id, comp_zero,
      Linear.smul_comp, Category.id_comp] using
      (show (r • 𝟙 (SC.obj F)) ≫ cokernel.π v = 0 from cokernel.condition v)
  have hker (j : ℤ) (U : X.ProEtᵒᵖ)
      (a : (completedIntegralCoefficientSheaf l E X D hl).obj.obj U)
      (ha : (completedIntegralCoefficientProjection l E X D hl n).hom.app U a = 0)
      (x : ((cokernel v).X j).val.obj U) : a • x = 0 := by
    obtain ⟨y, hy⟩ := AlgebraicGeometry.ProEtale.completedIntegralProjection_divisible
      l E X n U a ha
    have hz' := congrArg (fun z ↦ (z.f j).val.app U (y • x)) hscalar
    change (scalarSection l E X).val U ^ (n + 1) • (y • x) = 0 at hz'
    rw [hy, mul_smul]
    exact hz'
  obtain ⟨N, ⟨e⟩⟩ := complex_in_restriction_image
    (completedIntegralCoefficientProjection l E X D hl n) (hp n) (cokernel v) hker
  have himage : ∃ N, Nonempty (SC.obj (RC.obj N) ≅ cokernel v) :=
    ⟨N, ⟨iC.app N ≪≫ e⟩⟩
  let u : SC.obj F ⟶ SC.obj (RC.obj (EC.obj F)) := SC.map (adj.unit.app F)
  have hzero : r • 𝟙 (SC.obj (RC.obj (EC.obj F))) = 0 := by
    apply (cancel_mono (iC.hom.app (EC.obj F))).1
    have hzN : r • 𝟙 (NC.obj (EC.obj F)) = 0 := scalar_zero l E X D hl n (EC.obj F)
    simpa only [Linear.smul_comp, Linear.comp_smul, Category.id_comp, Category.comp_id,
      zero_comp, comp_zero] using
      congrArg (fun z ↦ iC.hom.app (EC.obj F) ≫ z) hzN
  have hzu : v ≫ u = 0 := by
    calc
      v ≫ u = u ≫ (r • 𝟙 (SC.obj (RC.obj (EC.obj F)))) := by
        change (r • 𝟙 (SC.obj F)) ≫ u = u ≫ (r • 𝟙 _)
        rw [Linear.smul_comp, Category.id_comp, Linear.comp_smul, Category.comp_id]
      _ = 0 := by rw [hzero, comp_zero]
  let d := cokernel.desc v u hzu
  have : IsIso d := unit_cokernel RC SC EC adj F v hzu himage
  have : PreservesFiniteLimits R := (normalizedDVRModuleRes_exact l E X h).1
  have : PreservesFiniteColimits R := (normalizedDVRModuleRes_exact l E X h).2
  have : QuasiIso (RC.map g) :=
    HomologicalComplex.quasiIso_map_of_preservesHomology g R
  have : PreservesFiniteLimits Sm := (completedIntegralRestrictScalars_exact l E X D hl m).1
  have : PreservesFiniteColimits Sm := (completedIntegralRestrictScalars_exact l E X D hl m).2
  have : QuasiIso (SC.map (RC.map g)) :=
    HomologicalComplex.quasiIso_map_of_preservesHomology (RC.map g) Sm
  have heq : cokernel.desc v (SC.map f ≫ iC.hom.app K) hz =
      d ≫ SC.map (RC.map g) ≫ iC.hom.app K := by
    apply (cancel_epi (cokernel.π v)).1
    rw [cokernel.π_desc, ← Category.assoc, ← Category.assoc, cokernel.π_desc,
      ← SC.map_comp]
    congr 2
    exact ((adj.homEquiv F K).apply_symm_apply f).symm
  change QuasiIso (cokernel.desc v (SC.map f ≫ iC.hom.app K) hz)
  rw [heq]
  infer_instance

end WeilConjectures
