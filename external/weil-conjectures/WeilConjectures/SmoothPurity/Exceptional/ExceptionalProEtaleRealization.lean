/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.SmoothPurity.Exceptional.ExceptionalFiniteRealization
public import WeilConjectures.AlgebraicGeometry.Pur.PurTwistSheafLocallyFree
public import WeilConjectures.AlgebraicGeometry.Sf.SfIntrinsicRealizationTransport
/-! # Finite coordinates and projections on the actual pro-etale systems
Source: blueprint theorem-f-shriek-finite-coefficients. The scalar-unit equations and
exact localization squares fix all comparisons, including their maps.
(blueprint: def-pur-adic-proetale-realization).
-/
@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry SheafOfModules
namespace WeilConjectures
private def scalarRestrictionCancel
    {C : Type (u + 1)} [Category.{u} C] {J : GrothendieckTopology C}
    {R S : Sheaf J RingCat.{u + 1}} (α : R ⟶ S) (β : S ⟶ R)
    (h : α ≫ β = 𝟙 R) :
    SheafOfModules.restrictScalars β ⋙ SheafOfModules.restrictScalars α ≅
      𝟭 (SheafOfModules.{u + 1} R) := by
  have hU (U : Cᵒᵖ) : (β.hom.app U).hom.comp (α.hom.app U).hom =
      RingHom.id (R.obj.obj U) :=
    congrArg RingCat.Hom.hom (congr_app (congrArg (fun k : R ⟶ R ↦ k.hom) h) U)
  refine NatIso.ofComponents (fun M ↦ (SheafOfModules.fullyFaithfulForget R).preimageIso
    (PresheafOfModules.isoMk (fun U ↦
      (ModuleCat.restrictScalarsComp'App (α.hom.app U).hom (β.hom.app U).hom
        (RingHom.id (R.obj.obj U)) (hU U).symm (M.val.obj U)).symm ≪≫
      (ModuleCat.restrictScalarsId (R.obj.obj U)).app (M.val.obj U)) ?_)) ?_
  · intro U V f
    ext x
    rfl
  · intro M N f
    ext U x
    rfl

private theorem scalarRestrictionEquivalence
    {C : Type (u + 1)} [Category.{u} C] {J : GrothendieckTopology C}
    {R S : Sheaf J RingCat.{u + 1}} (e : R ≅ S) :
    (SheafOfModules.restrictScalars.{u + 1} e.hom).IsEquivalence :=
  (CategoryTheory.Equivalence.mk (SheafOfModules.restrictScalars.{u + 1} e.hom)
    (SheafOfModules.restrictScalars e.inv)
    (scalarRestrictionCancel e.inv e.hom e.inv_hom_id).symm
    (scalarRestrictionCancel e.hom e.inv e.hom_inv_id)).isEquivalence_functor

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- The quotient ring is finite at every positive exponent.
Source: blueprint finite coefficients (blueprint: def-pur-adic-proetale-realization). -/
instance integralExceptionalFiniteQuotient (n : ℕ) :
    Finite (Padic.coefficientExtensionRing l E (n + 1)) :=
  Padic.finite_coefficientExtensionRing l E (n + 1) (Nat.succ_le_succ (Nat.zero_le n))

/-- Finite realization on the pro-etale site, using only scalar restriction and the
explicit quotient equivalence. It retains each underlying section.
Source: blueprint integral exceptional image (blueprint: def-pur-adic-proetale-realization). -/
def integralExceptionalProRealization (W : Scheme.{u}) (n : ℕ) :
    coefficientLevelModules (J := Scheme.ProEt.topology W)
      (integralExceptionalIntegers l E) (integralExceptionalUniformizer l E) n ⥤
    Sheaf (Scheme.ProEt.topology W)
      (ModuleCat.{u + 1} (ULift.{u + 1} (Padic.coefficientExtensionRing l E (n + 1)))) :=
  letI := Scheme.purTwistForgetPreservesSheafification W
  SheafOfModules.restrictScalars
      ((constantCommuteCompose (Scheme.ProEt.topology W)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).app
          (CommRingCat.of (integralExceptionalQuotientRing l E n))).inv ⋙
    constantRingModuleRestriction (Scheme.ProEt.topology W)
      (integralExceptionalQuotientRing l E n) ⋙
      sheafCompose (Scheme.ProEt.topology W)
        (ModuleCat.restrictScalars (integralExceptionalQuotient l E n).symm.toRingHom)

/-- Pro-etale finite realization is an exact additive equivalence.
Source: blueprint integral exceptional image (blueprint: def-pur-adic-proetale-realization).
Proof: its factors are restriction along the constant-ring presentation isomorphism,
the equivalence extending constant scalar actions to locally constant sections, and
restriction along a ring equivalence. Their inverses undo those operations. They
leave underlying maps unchanged and preserve kernels and cokernels. -/
theorem integralExceptionalProRealization_properties (W : Scheme.{u}) (n : ℕ) :
    (integralExceptionalProRealization l E W n).IsEquivalence ∧
      (integralExceptionalProRealization l E W n).Additive ∧
      PreservesFiniteLimits (integralExceptionalProRealization l E W n) ∧
      PreservesFiniteColimits (integralExceptionalProRealization l E W n) := by
  let := Scheme.purTwistForgetPreservesSheafification W
  obtain ⟨e, he, ha, _, _⟩ :=
    (constant_ring_module_sheaves (Scheme.ProEt.topology W)
      (integralExceptionalQuotientRing l E n)).1
  have : (constantRingModuleRestriction (Scheme.ProEt.topology W)
      (integralExceptionalQuotientRing l E n)).IsEquivalence := he ▸ e.isEquivalence_functor
  have : (constantRingModuleRestriction (Scheme.ProEt.topology W)
      (integralExceptionalQuotientRing l E n)).Additive := he ▸ ha
  let c := (constantCommuteCompose (Scheme.ProEt.topology W)
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).app
      (CommRingCat.of (integralExceptionalQuotientRing l E n))
  have : (SheafOfModules.restrictScalars.{u + 1} c.inv).IsEquivalence :=
    scalarRestrictionEquivalence c.symm
  have : (ModuleCat.restrictScalars.{u + 1}
      (integralExceptionalQuotient l E n).symm.toRingHom).IsEquivalence :=
    ModuleCat.restrictScalars_isEquivalence_of_ringEquiv
      (integralExceptionalQuotient l E n).symm
  have : (sheafCompose (Scheme.ProEt.topology W) (ModuleCat.restrictScalars.{u + 1}
      (integralExceptionalQuotient l E n).symm.toRingHom)).IsEquivalence :=
    isEquivalence_sheafCompose_of_isEquivalence _ _
  have hE : (integralExceptionalProRealization l E W n).IsEquivalence := by
    dsimp only [integralExceptionalProRealization]
    infer_instance
  have hA : (integralExceptionalProRealization l E W n).Additive :=
    Functor.additive_of_preserves_binary_products _
  exact ⟨hE, hA, inferInstance, inferInstance⟩
/-- Instance induced by the preceding named construction or property.
Source: blueprint adic reconstruction, canonical coefficient comparisons
(blueprint: def-pur-adic-proetale-realization). -/
instance integralExceptionalProRealization_equivalence (W : Scheme.{u}) (n : ℕ) :
    (integralExceptionalProRealization l E W n).IsEquivalence :=
  (integralExceptionalProRealization_properties l E W n).1
/-- Instance induced by the preceding named construction or property.
Source: blueprint adic reconstruction, canonical coefficient comparisons
(blueprint: def-pur-adic-proetale-realization). -/
instance integralExceptionalProRealization_additive (W : Scheme.{u}) (n : ℕ) :
    (integralExceptionalProRealization l E W n).Additive :=
  (integralExceptionalProRealization_properties l E W n).2.1
/-- Instance induced by the preceding named construction or property.
Source: blueprint adic reconstruction, canonical coefficient comparisons
(blueprint: def-pur-adic-proetale-realization). -/
instance integralExceptionalProRealization_limits (W : Scheme.{u}) (n : ℕ) :
    PreservesFiniteLimits (integralExceptionalProRealization l E W n) :=
  (integralExceptionalProRealization_properties l E W n).2.2.1
/-- Instance induced by the preceding named construction or property.
Source: blueprint adic reconstruction, canonical coefficient comparisons
(blueprint: def-pur-adic-proetale-realization). -/
instance integralExceptionalProRealization_colimits (W : Scheme.{u}) (n : ℕ) :
    PreservesFiniteColimits (integralExceptionalProRealization l E W n) :=
  (integralExceptionalProRealization_properties l E W n).2.2.2

variable (W : Scheme.{u})

/-- Cache existing sheafification at the precise site size.
Source: blueprint integral coefficients (blueprint: def-pur-adic-proetale-realization). -/
instance (priority := 4000) integralExceptionalProRingRightAdjoint :
    (sheafToPresheaf (Scheme.ProEt.topology W) CommRingCat.{u + 1}).IsRightAdjoint :=
  inferInstance
/-- Restriction along the explicit ring map preserves addition.
Source: blueprint integral coefficients (blueprint: def-pur-adic-proetale-realization). -/
instance integralExceptionalLevel_additive (n : ℕ) :
    (integralExceptionalLevel l E W n).Additive :=
  inferInstanceAs (SheafOfModules.restrictScalars.{u + 1}
    (integralExceptionalRingMap l E W n)).Additive
/-- Cache componentwise addition at the actual system sizes.
Source: blueprint integral coefficients (blueprint: def-pur-adic-proetale-realization). -/
instance (priority := 4000) integralExceptionalEvaluation_additive :
    ∀ n, (coefficientEvaluation.{u + 1, u, u + 1}
      (J := Scheme.ProEt.topology W) (O := integralExceptionalIntegers l E)
      (ell := integralExceptionalUniformizer l E) n).Additive :=
  fun n ↦ coefficientEvaluation_additive.{u + 1, u, u + 1} n
/-- Componentwise kernels are preserved by evaluation.
Source: blueprint integral coefficients (blueprint: def-pur-adic-proetale-realization). -/
instance integralExceptionalEvaluation_limits (n : ℕ) :
    PreservesFiniteLimits (coefficientEvaluation.{u + 1, u, u + 1} (J := Scheme.ProEt.topology W)
      (O := integralExceptionalIntegers l E) (ell := integralExceptionalUniformizer l E) n) :=
  (coefficientEvaluation_exact.{u + 1, u, u + 1}
    (J := Scheme.ProEt.topology W) (O := integralExceptionalIntegers l E)
    (ell := integralExceptionalUniformizer l E) n).1
/-- Componentwise cokernels are preserved by evaluation.
Source: blueprint integral coefficients (blueprint: def-pur-adic-proetale-realization). -/
instance integralExceptionalEvaluation_colimits (n : ℕ) :
    PreservesFiniteColimits (coefficientEvaluation.{u + 1, u, u + 1} (J := Scheme.ProEt.topology W)
      (O := integralExceptionalIntegers l E) (ell := integralExceptionalUniformizer l E) n) :=
  (coefficientEvaluation_exact.{u + 1, u, u + 1}
    (J := Scheme.ProEt.topology W) (O := integralExceptionalIntegers l E)
    (ell := integralExceptionalUniformizer l E) n).2

/-- The original finite-to-generic coordinate change is itself an equivalence.
Source: blueprint integral exceptional image (blueprint: def-pur-adic-proetale-realization).
Proof: the ring map is induced by the explicit quotient ring equivalence. Restriction
along its inverse is a two-sided inverse on module sheaves. -/
theorem integralExceptionalLevel_equivalence (n : ℕ) :
    (integralExceptionalLevel l E W n).IsEquivalence := by
  let e := (sheafCompose (Scheme.ProEt.topology W)
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).mapIso
      ((constantSheaf (Scheme.ProEt.topology W) CommRingCat.{u + 1}).mapIso
        (integralExceptionalQuotient l E n).toCommRingCatIso)
  exact scalarRestrictionEquivalence e
attribute [instance] integralExceptionalLevel_equivalence

private theorem constantRingScalar
    {C : Type*} [Category* C] (J : GrothendieckTopology C)
    [HasWeakSheafify J RingCat.{u + 1}] [HasWeakSheafify J CommRingCat.{u + 1}]
    [J.PreservesSheafification (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})]
    [J.HasSheafCompose (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})]
    (A : Type (u + 1)) [CommRing A] (U : Cᵒᵖ) (a : A) :
    (((constantCommuteCompose J (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).inv.app
      (CommRingCat.of A)).hom.app U)
      ((toSheafify J ((Functor.const Cᵒᵖ).obj (RingCat.of A))).app U a) =
    (toSheafify J ((Functor.const Cᵒᵖ).obj (CommRingCat.of A))).app U a := by
  have h := sheafComposeIso_hom_fac J (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})
    ((Functor.const Cᵒᵖ).obj (CommRingCat.of A))
  change ((sheafifyComposeIso J (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})
    ((Functor.const Cᵒᵖ).obj (CommRingCat.of A))).hom.app U)
      (((presheafToSheaf J RingCat.{u + 1}).map
        ((Functor.compConstIso Cᵒᵖ
          (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).hom.app
            (CommRingCat.of A))).hom.app U
              ((toSheafify J ((Functor.const Cᵒᵖ).obj (RingCat.of A))).app U a)) = _
  have hi : ((Functor.compConstIso Cᵒᵖ
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).hom.app
        (CommRingCat.of A)) = 𝟙 _ := rfl
  rw [hi, CategoryTheory.Functor.map_id]
  exact congrArg (fun f ↦ f.app U a) h

attribute [local instance] Scheme.purTwistForgetPreservesSheafification

private theorem coordinateScalarUnit (n : ℕ) (U : W.ProEtᵒᵖ)
    (a : ULift.{u + 1} (Padic.coefficientExtensionRing l E (n + 1))) :
    ((integralExceptionalRingMap l E W n).hom.app U)
      ((((constantCommuteCompose (Scheme.ProEt.topology W)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).app
          (CommRingCat.of (integralExceptionalQuotientRing l E n))).inv.hom.app U)
            ((toSheafify (Scheme.ProEt.topology W)
              ((Functor.const W.ProEtᵒᵖ).obj
                (RingCat.of (integralExceptionalQuotientRing l E n)))).app U
                  ((integralExceptionalQuotient l E n).symm a))) =
      (ProEtale.finiteCoefficientIntrinsicScalarMap W
        (Padic.coefficientExtensionRing l E (n + 1)) ).app U a := by
  have hc := constantRingScalar (Scheme.ProEt.topology W)
    (integralExceptionalQuotientRing l E n) U ((integralExceptionalQuotient l E n).symm a)
  change ((integralExceptionalRingMap l E W n).hom.app U) _ = _
  apply Eq.trans (congrArg (fun x ↦
    ((integralExceptionalRingMap l E W n).hom.app U) x) hc)
  have h := toSheafify_naturality (Scheme.ProEt.topology W)
    ((Functor.const W.ProEtᵒᵖ).map
      (CommRingCat.ofHom (integralExceptionalQuotient l E n).toRingHom))
  have h' := congrArg
    (fun f ↦ f.app U ((integralExceptionalQuotient l E n).symm a)) h
  change (ProEtale.finiteCoefficientIntrinsicScalarMap W
    (Padic.coefficientExtensionRing l E (n + 1))).app U
      ((integralExceptionalQuotient l E n) ((integralExceptionalQuotient l E n).symm a)) =
    ((integralExceptionalRingMap l E W n).hom.app U)
      ((toSheafify (Scheme.ProEt.topology W)
        ((Functor.const W.ProEtᵒᵖ).obj
          (CommRingCat.of (integralExceptionalQuotientRing l E n)))).app U
            ((integralExceptionalQuotient l E n).symm a)) at h'
  rw [RingEquiv.apply_symm_apply] at h'
  exact h'.symm

private theorem scalarUnit_bijective (n : ℕ)
    (M : Sheaf (Scheme.ProEt.topology W)
      (ModuleCat.{u + 1} (ULift.{u + 1} (Padic.coefficientExtensionRing l E (n + 1)))))
    (U : W.ProEtᵒᵖ) :
    Function.Bijective (Scheme.sfIntrinsicRealizationUnit W
      (Padic.coefficientExtensionRing l E (n + 1)) M U) := by
  let α := ProEtale.finiteCoefficientIntrinsicScalarMap W
    (Padic.coefficientExtensionRing l E (n + 1))
  let N := (ProEtale.finiteCoefficientModulePresheaf W.ProEt
    (ULift.{u + 1} (Padic.coefficientExtensionRing l E (n + 1)))).obj M.obj
  let η := (PresheafOfModules.sheafificationAdjunction α).unit.app N
  have : IsIso η := by
    dsimp only [η, α, N]
    rw [← isIso_iff_of_reflects_iso _ (PresheafOfModules.toPresheaf _)]
    simp only [PresheafOfModules.toPresheaf_map_sheafificationAdjunction_unit_app]
    apply isIso_toSheafify
    exact ((sheafCompose (Scheme.ProEt.topology W)
      (forget₂ (ModuleCat.{u + 1}
        (ULift.{u + 1} (Padic.coefficientExtensionRing l E (n + 1))))
          AddCommGrpCat.{u + 1})).obj M).property
  have : IsIso (η.app U) := inferInstanceAs
    (IsIso ((PresheafOfModules.evaluation _ U).map η))
  exact ConcreteCategory.bijective_of_isIso (η.app U)

private def coordinateUnit (n : ℕ) :
    𝟭 _ ⟶ (Scheme.sfIntrinsicModuleEquivalence W
      (Padic.coefficientExtensionRing l E (n + 1))).functor ⋙
        integralExceptionalLevel l E W n ⋙ integralExceptionalProRealization l E W n where
  app M := { hom :=
    { app := fun U ↦ ModuleCat.ofHom
        (X := M.obj.obj U)
        (Y := (((Scheme.sfIntrinsicModuleEquivalence W
          (Padic.coefficientExtensionRing l E (n + 1))).functor ⋙
            integralExceptionalLevel l E W n ⋙ integralExceptionalProRealization l E W n).obj
              M).obj.obj U)
        { toFun := Scheme.sfIntrinsicRealizationUnit W
            (Padic.coefficientExtensionRing l E (n + 1)) M U
          map_add' := by
            intro x y
            exact map_add _ x y
          map_smul' := by
            intro a x
            change Scheme.sfIntrinsicRealizationUnit W
              (Padic.coefficientExtensionRing l E (n + 1)) M U (a • x) = _
            have h := ((PresheafOfModules.sheafificationAdjunction
              (ProEtale.finiteCoefficientIntrinsicScalarMap W
                (Padic.coefficientExtensionRing l E (n + 1)))).unit.app
                  ((ProEtale.finiteCoefficientModulePresheaf W.ProEt
                    (ULift.{u + 1} (Padic.coefficientExtensionRing l E (n + 1)))).obj
                      M.obj)).app U |>.hom.map_smul a x
            change _ = (ProEtale.finiteCoefficientIntrinsicScalarMap W
              (Padic.coefficientExtensionRing l E (n + 1))).app U a •
                Scheme.sfIntrinsicRealizationUnit W
                  (Padic.coefficientExtensionRing l E (n + 1)) M U x at h
            exact h.trans (congrArg (fun s ↦ s •
              Scheme.sfIntrinsicRealizationUnit W
                (Padic.coefficientExtensionRing l E (n + 1)) M U x)
                  (coordinateScalarUnit l E W n U a).symm) }
      naturality := by
        intro U V f
        ext x
        exact PresheafOfModules.naturality_apply
          ((PresheafOfModules.sheafificationAdjunction
            (ProEtale.finiteCoefficientIntrinsicScalarMap W
              (Padic.coefficientExtensionRing l E (n + 1)))).unit.app
                ((ProEtale.finiteCoefficientModulePresheaf W.ProEt
                  (ULift.{u + 1} (Padic.coefficientExtensionRing l E (n + 1)))).obj M.obj)) f x } }
  naturality := by
    intro M N f
    ext U x
    exact ConcreteCategory.congr_hom
      (congrArg (fun h ↦ h.app U)
        ((PresheafOfModules.sheafificationAdjunction
          (ProEtale.finiteCoefficientIntrinsicScalarMap W
            (Padic.coefficientExtensionRing l E (n + 1)))).unit.naturality
              ((ProEtale.finiteCoefficientModulePresheaf W.ProEt
                (ULift.{u + 1} (Padic.coefficientExtensionRing l E (n + 1)))).map f.hom))) x

/-- The coordinate realization of a fixed module is the same module. Its map is
specified on every scalar-unit section of the actual intrinsic realization.
Source: blueprint integral exceptional image (blueprint: def-pur-adic-proetale-realization).
Proof: restriction leaves the underlying abelian sheaf unchanged. The scalar-unit
map becomes an isomorphism after extending and then restricting locally constant
coefficients. Its inverse satisfies the displayed section formula. Such sections
locally generate, so the natural isomorphism is unique. -/
theorem integralExceptionalFixedUnit_existsUnique (n : ℕ) :
    ∃! e : (Scheme.sfIntrinsicModuleEquivalence W
        (Padic.coefficientExtensionRing l E (n + 1))).functor ⋙
      integralExceptionalLevel l E W n ⋙ integralExceptionalProRealization l E W n ≅ 𝟭 _,
      ∀ (M : Sheaf (Scheme.ProEt.topology W)
        (ModuleCat.{u + 1} (ULift.{u + 1} (Padic.coefficientExtensionRing l E (n + 1)))))
        (U : W.ProEtᵒᵖ) (m : M.obj.obj U),
        (e.hom.app M).hom.app U
          (Scheme.sfIntrinsicRealizationUnit W
            (Padic.coefficientExtensionRing l E (n + 1)) M U m) = m := by
  let t := coordinateUnit l E W n
  have : IsIso t := by
    rw [NatTrans.isIso_iff_isIso_app]
    intro M
    rw [← isIso_iff_of_reflects_iso _ (sheafToPresheaf _ _)]
    rw [NatTrans.isIso_iff_isIso_app]
    intro U
    exact (ConcreteCategory.isIso_iff_bijective _).mpr (scalarUnit_bijective l E W n M U)
  let e := (asIso t).symm
  have he : ∀ M U m, (e.hom.app M).hom.app U
      (Scheme.sfIntrinsicRealizationUnit W
        (Padic.coefficientExtensionRing l E (n + 1)) M U m) = m := by
    intro M U m
    exact ConcreteCategory.congr_hom
      (congr_app (congrArg (fun f ↦ f.hom) ((asIso t).hom_inv_id_app M)) U) m
  refine ⟨e, he, ?_⟩
  intro e' he'
  apply Iso.ext
  ext M U x
  obtain ⟨m, rfl⟩ := (scalarUnit_bijective l E W n M U).surjective x
  exact (he' M U m).trans (he M U m).symm

/-- The actual scalar-unit-normalized finite coordinate realization.
Source: blueprint integral exceptional image (blueprint: def-pur-adic-proetale-realization). -/
def integralExceptionalFixedUnit (n : ℕ) :=
  (integralExceptionalFixedUnit_existsUnique l E W n).exists.choose

/-- Identification with the recorded inverse realization, normalized by its unit.
Source: blueprint integral exceptional image (blueprint: def-pur-adic-proetale-realization).
Proof: compose the preceding scalar-unit comparison with the unit and counit of the
recorded realization equivalence. Its triangle identities give the displayed equation.Essential
 surjectivity of the realization and its unit determine every component. -/
theorem integralExceptionalLevelFixed_existsUnique (n : ℕ) :
    ∃! e : integralExceptionalLevel l E W n ⋙ integralExceptionalProRealization l E W n ≅
      (Scheme.sfIntrinsicModuleEquivalence W
        (Padic.coefficientExtensionRing l E (n + 1))).inverse,
      ∀ M, e.hom.app ((Scheme.sfIntrinsicModuleEquivalence W
        (Padic.coefficientExtensionRing l E (n + 1))).functor.obj M) ≫
        (Scheme.sfIntrinsicModuleEquivalence W
          (Padic.coefficientExtensionRing l E (n + 1))).unitIso.inv.app M =
          (integralExceptionalFixedUnit l E W n).hom.app M := by
  let e := Scheme.sfIntrinsicModuleEquivalence W
    (Padic.coefficientExtensionRing l E (n + 1))
  let G := integralExceptionalLevel l E W n ⋙ integralExceptionalProRealization l E W n
  let C := Sheaf (Scheme.ProEt.topology W)
    (ModuleCat.{u + 1} (ULift.{u + 1} (Padic.coefficientExtensionRing l E (n + 1))))
  let D := Scheme.proEtaleRingModules W
    (Scheme.proEtaleConstantRing W (Padic.coefficientExtensionRing l E (n + 1)))
  let H := (Functor.whiskeringLeft C D C).obj e.functor
  let hH := Functor.FullyFaithful.ofFullyFaithful H
  let t : H.obj G ≅ H.obj e.inverse :=
    integralExceptionalFixedUnit l E W n ≪≫ e.unitIso
  let a : G ≅ e.inverse := hH.preimageIso t
  have ha (M) : a.hom.app (e.functor.obj M) = t.hom.app M := by
    exact congr_app (hH.map_preimage t.hom) M
  have hnorm (M : C) : a.hom.app (e.functor.obj M) ≫ e.unitIso.inv.app M =
      (integralExceptionalFixedUnit l E W n).hom.app M := by
    rw [ha]
    simp only [t, Iso.trans_hom, NatTrans.comp_app, Category.assoc, Iso.hom_inv_id_app,
      Category.comp_id]
  refine ⟨a, hnorm, ?_⟩
  intro b hb
  apply Iso.ext
  apply H.map_injective
  apply NatTrans.ext
  funext M
  change b.hom.app (e.functor.obj M) = a.hom.app (e.functor.obj M)
  apply (Iso.cancel_iso_hom_right _ _ (e.unitIso.app M).symm).mp
  exact (hb M).trans (hnorm M).symm

/-- The finite coordinate comparison, fixed by the recorded equivalence unit.
Source: blueprint integral exceptional image (blueprint: def-pur-adic-proetale-realization). -/
def integralExceptionalLevelFixed (n : ℕ) :=
  (integralExceptionalLevelFixed_existsUnique l E W n).exists.choose

/-- The exact derived coordinate comparison, induced by the specified ordinary map.
Source: blueprint integral exceptional image (blueprint: def-pur-adic-proetale-realization). -/
def integralExceptionalDerivedLevelFixed (n : ℕ) :
    (integralExceptionalLevel l E W n).mapDerivedCategory ⋙
      (integralExceptionalProRealization l E W n).mapDerivedCategory ≅
    (Scheme.sfIntrinsicDerivedEquivalence W
      (Padic.coefficientExtensionRing l E (n + 1))).inverse :=
  letI := (Scheme.sfIntrinsicModuleEquivalence W
    (Padic.coefficientExtensionRing l E (n + 1))).inverse_additive
  Functor.mapDerivedCategoryCompIso _ _ ≪≫
    Functor.mapDerivedCategoryNatIso (integralExceptionalLevelFixed l E W n)

/-- Coordinates preserve finite evaluation as an equality of actual ordinary functors.
Source: blueprint integral exceptional image (blueprint: def-pur-adic-proetale-realization).
Proof: both functors take a strict system to its nth module with the quotient action
changed along the same ring equivalence. Their maps are the same nth component map;
functor extensionality gives equality. -/
theorem integralExceptionalCoordinatesEvaluation (n : ℕ) :
    integralExceptionalCoordinates l E W ⋙
      coefficientEvaluation.{u + 1, u, u + 1} (J := Scheme.ProEt.topology W)
        (O := integralExceptionalIntegers l E) (ell := integralExceptionalUniformizer l E) n =
    coefficientSequenceEvaluation l E W n ⋙ integralExceptionalLevel l E W n := by
  rfl

/-- Every normalized evaluation package has its unique exact-localization comparison.
Source: blueprint integral exceptional image (blueprint: def-pur-adic-proetale-realization).
Proof: both functors factor termwise evaluation through quasi-isomorphism localization. The
two displayed factorization maps give existence. Uniqueness of factorization on
complexes and roofs proves uniqueness of the natural isomorphism. -/
theorem integralExceptionalProEvaluationModel_existsUnique
    (P : CoefficientEvaluationDerivedPackage.{u + 1, u, u + 1, u + 2} (J := Scheme.ProEt.topology W)
      (O := integralExceptionalIntegers l E) (ell := integralExceptionalUniformizer l E))
    (n : ℕ) :
    ∃! e : P.evaluation n ≅
      (coefficientEvaluation.{u + 1, u, u + 1} (J := Scheme.ProEt.topology W)
        (O := integralExceptionalIntegers l E) (ell := integralExceptionalUniformizer l E)
          n).mapDerivedCategory
          ,
      ∀ J, e.hom.app (DerivedCategory.Q.obj J) ≫
        (coefficientEvaluation.{u + 1, u, u + 1} (J := Scheme.ProEt.topology W)
          (O := integralExceptionalIntegers l E) (ell := integralExceptionalUniformizer l E)
            n).mapDerivedCategoryFactors.hom.app
             J = (P.evaluationFactors n).hom.app J := by
  let F := coefficientEvaluation.{u + 1, u, u + 1} (J := Scheme.ProEt.topology W)
    (O := integralExceptionalIntegers l E) (ell := integralExceptionalUniformizer l E) n
  let e : P.evaluation n ≅ F.mapDerivedCategory :=
    Localization.liftNatIso DerivedCategory.Q
      (HomologicalComplex.quasiIso _ (.up ℤ))
      (DerivedCategory.Q ⋙ P.evaluation n) (DerivedCategory.Q ⋙ F.mapDerivedCategory)
      (P.evaluation n) F.mapDerivedCategory
      (P.evaluationFactors n ≪≫ F.mapDerivedCategoryFactors.symm)
  have he : ∀ J, e.hom.app (DerivedCategory.Q.obj J) ≫
      F.mapDerivedCategoryFactors.hom.app J = (P.evaluationFactors n).hom.app J := by
    intro J
    dsimp [e]
    simp only [Localization.liftNatIso_hom, Localization.liftNatTrans_app,
      Localization.Lifting.compLeft, Iso.refl_hom, Iso.refl_inv, NatTrans.id_app,
      Category.id_comp, Category.comp_id, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
      Category.assoc, Iso.inv_hom_id_app, Category.comp_id]
  refine ⟨e, he, ?_⟩
  intro e' he'
  apply Iso.ext
  apply Localization.natTrans_ext DerivedCategory.Q (HomologicalComplex.quasiIso _ (.up ℤ))
  intro J
  apply (cancel_mono (F.mapDerivedCategoryFactors.hom.app J)).mp
  exact (he' J).trans (he J).symm

/-- The evaluation model, fixed on every strict complex.
Source: blueprint integral exceptional image (blueprint: def-pur-adic-proetale-realization). -/
@[no_expose] def integralExceptionalProEvaluationModel
    (P : CoefficientEvaluationDerivedPackage.{u + 1, u, u + 1, u + 2} (J := Scheme.ProEt.topology W)
      (O := integralExceptionalIntegers l E) (ell := integralExceptionalUniformizer l E))
    (n : ℕ) :=
  (integralExceptionalProEvaluationModel_existsUnique l E W P n).exists.choose

/-- The direct coordinate/evaluation identification, obtained from the exact ordinary
coordinate equality and the scalar-unit-normalized finite realization.
Source: blueprint integral exceptional image (blueprint: def-pur-adic-proetale-realization). -/
@[no_expose] def integralExceptionalCoordinatesFixed
    (P : CoefficientEvaluationDerivedPackage.{u + 1, u, u + 1, u + 2} (J := Scheme.ProEt.topology W)
      (O := integralExceptionalIntegers l E) (ell := integralExceptionalUniformizer l E))
    (N : coefficientSequenceDerived l E W) (n : ℕ) :
    (integralExceptionalProRealization l E W n).mapDerivedCategory.obj
      ((P.evaluation n).obj ((integralExceptionalDerivedCoordinates l E W).obj N)) ≅
    (Scheme.sfIntrinsicDerivedEquivalence W
      (Padic.coefficientExtensionRing l E (n + 1))).inverse.obj
        ((coefficientSequenceDerivedEvaluation l E W n).obj N) :=
  (integralExceptionalProRealization l E W n).mapDerivedCategory.mapIso
    ((integralExceptionalProEvaluationModel l E W P n).app _ ≪≫
      (Functor.mapDerivedCategoryCompIso _ _).app N ≪≫
      (Functor.mapDerivedCategoryNatIso
        (eqToIso (integralExceptionalCoordinatesEvaluation l E W n))).app N ≪≫
      (Functor.mapDerivedCategoryCompIso _ _).symm.app N) ≪≫
    (integralExceptionalDerivedLevelFixed l E W n).app _

/-- The inverse coordinate/evaluation identification uses the actual counit of the
coordinate equivalence, rather than any choice of levelwise lift.
Source: blueprint integral exceptional image (blueprint: def-pur-adic-proetale-realization). -/
@[no_expose] def integralExceptionalCoordinatesInvFixed
    (P : CoefficientEvaluationDerivedPackage.{u + 1, u, u + 1, u + 2} (J := Scheme.ProEt.topology W)
      (O := integralExceptionalIntegers l E) (ell := integralExceptionalUniformizer l E))
    (N : DerivedCategory (CoefficientSystem (J := Scheme.ProEt.topology W)
      (integralExceptionalIntegers l E) (integralExceptionalUniformizer l E))) (n : ℕ) :
    (Scheme.sfIntrinsicDerivedEquivalence W
      (Padic.coefficientExtensionRing l E (n + 1))).inverse.obj
      ((coefficientSequenceDerivedEvaluation l E W n).obj
        ((integralExceptionalDerivedCoordinatesInv l E W).obj N)) ≅
    (integralExceptionalProRealization l E W n).mapDerivedCategory.obj ((P.evaluation n).obj N) :=
  letI : (integralExceptionalCoordinates l E W).asEquivalence.functor.Additive :=
    integralExceptionalCoordinates_additive l E W
  (integralExceptionalCoordinatesFixed l E W P
    ((integralExceptionalDerivedCoordinatesInv l E W).obj N) n).symm ≪≫
    (integralExceptionalProRealization l E W n).mapDerivedCategory.mapIso
      ((P.evaluation n).mapIso
        (((integralExceptionalCoordinates l E W).asEquivalence.mapDerivedCategory).counitIso.app
           N))
end WeilConjectures
