/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.Sf.SfFiniteOpenRestrictionPresentation
import WeilConjectures.SmoothPurity.Sf.SfIntrinsicOpenUnitGenerators

/-! # Coefficient restriction on finite open extension generators

Source: Stacks Tags 03DI, 03DJ and 0E8I.
(blueprint: lem-sf-finite-open-coefficient-generators).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u v w
open CategoryTheory Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- The quotient in the slice tower is the specified adjacent coefficient quotient.
Source: Bhatt--Scholze, Definition 3.5.2; Stacks 03DA
(blueprint: lem-sf-finite-open-coefficient-generators). -/
theorem sfFiniteOpenPresentation_restriction_eq (T : Scheme.{u}) (n : ℕ) :
    normalizedDVRModuleRes l E T (Nat.le_succ n) =
      sfCompactSupportFiniteRestriction l E T n := by
  unfold normalizedDVRModuleRes normalizedDVRQuotient integralCoefficientSheafSystem
  rw [Functor.ofOpSequence_map_homOfLE_succ]
  rfl

/-- Change only the presentation of the same adjacent restriction functor.
Source: Stacks 03DA (blueprint: lem-sf-finite-open-coefficient-generators). -/
def sfFiniteOpenPresentationRestriction (T : Scheme.{u}) (n : ℕ) :
    normalizedDVRModuleRes l E T (Nat.le_succ n) ≅
      sfCompactSupportFiniteRestriction l E T n :=
  eqToIso (sfFiniteOpenPresentation_restriction_eq l E T n)

/-- Restriction along an arbitrary ring-sheaf map leaves the section carrier unchanged.
Source: Stacks 03DA (blueprint: lem-sf-finite-open-coefficient-generators). -/
@[irreducible] def sfSheafScalarSection (T : Scheme.{u})
    {R S : Sheaf (ProEt.topology T) RingCat.{u + 1}} (φ : R ⟶ S)
    (N : SheafOfModules.{u + 1} S) (W : T.ProEtᵒᵖ) (x : N.val.obj W) :
    ((SheafOfModules.restrictScalars φ).obj N).val.obj W := x

/-- The inverse identity on carriers, with the ring-sheaf map kept abstract.
Source: Stacks 03DA (blueprint: lem-sf-finite-open-coefficient-generators). -/
@[irreducible] def sfSheafUnscalarSection (T : Scheme.{u})
    {R S : Sheaf (ProEt.topology T) RingCat.{u + 1}} (φ : R ⟶ S)
    (N : SheafOfModules.{u + 1} S) (W : T.ProEtᵒᵖ)
    (x : ((SheafOfModules.restrictScalars φ).obj N).val.obj W) : N.val.obj W := x

/-- Convert a heterogeneous section-function identity using the explicit carrier maps.
Source: Stacks 03DA (blueprint: lem-sf-finite-open-coefficient-generators). -/
private theorem sfSheafSection_heq (T U : Scheme.{u})
    {R S : Sheaf (ProEt.topology T) RingCat.{u + 1}} (φ : R ⟶ S)
    {R' S' : Sheaf (ProEt.topology U) RingCat.{u + 1}} (ψ : R' ⟶ S')
    (M : SheafOfModules.{u + 1} S) (N : SheafOfModules.{u + 1} S')
    (V : T.ProEtᵒᵖ) (W : U.ProEtᵒᵖ)
    {f : ((SheafOfModules.restrictScalars φ).obj M).val.obj V →
      ((SheafOfModules.restrictScalars ψ).obj N).val.obj W}
    {g : M.val.obj V → N.val.obj W} (h : HEq f g)
    (x : ((SheafOfModules.restrictScalars φ).obj M).val.obj V) :
    f x = sfSheafScalarSection U ψ N W (g (sfSheafUnscalarSection T φ M V x)) := by
  unfold sfSheafScalarSection sfSheafUnscalarSection
  exact congrFun (eq_of_heq h) x

/-- The generic carrier identity, instantiated at a normalized coefficient quotient.
Source: Stacks 03DA (blueprint: lem-sf-finite-open-coefficient-generators). -/
@[irreducible] def sfNormalizedDVRSection (T : Scheme.{u}) {m n : ℕ} (h : n ≤ m)
    (N : normalizedDVRModules l E T n) (W : T.ProEtᵒᵖ) (x : N.val.obj W) :
    ((normalizedDVRModuleRes l E T h).obj N).val.obj W :=
  sfSheafScalarSection T (normalizedDVRQuotient l E T h) N W x

/-- The inverse carrier identity at a normalized coefficient quotient.
Source: Stacks 03DA (blueprint: lem-sf-finite-open-coefficient-generators). -/
@[irreducible] def sfNormalizedDVRUnsection (T : Scheme.{u}) {m n : ℕ} (h : n ≤ m)
    (N : normalizedDVRModules l E T n) (W : T.ProEtᵒᵖ)
    (x : ((normalizedDVRModuleRes l E T h).obj N).val.obj W) : N.val.obj W :=
  sfSheafUnscalarSection T (normalizedDVRQuotient l E T h) N W x

/-- The heterogeneous section law in the normalized quotient presentation.
Source: Stacks 03DA (blueprint: lem-sf-finite-open-coefficient-generators).
Proof: unfold only the two quotient-carrier wrappers and use the generic
ring-sheaf section identity, keeping both quotient maps as parameters. -/
theorem sfNormalizedDVRSection_heq (T U : Scheme.{u}) (n : ℕ)
    (M : normalizedDVRModules l E T n) (N : normalizedDVRModules l E U n)
    (V : T.ProEtᵒᵖ) (W : U.ProEtᵒᵖ)
    {f : ((normalizedDVRModuleRes l E T (Nat.le_succ n)).obj M).val.obj V →
      ((normalizedDVRModuleRes l E U (Nat.le_succ n)).obj N).val.obj W}
    {g : M.val.obj V → N.val.obj W} (h : HEq f g)
    (x : ((normalizedDVRModuleRes l E T (Nat.le_succ n)).obj M).val.obj V) :
    f x = sfNormalizedDVRSection l E U (Nat.le_succ n) N W
      (g (sfNormalizedDVRUnsection l E T (Nat.le_succ n) M V x)) := by
  unfold sfNormalizedDVRSection sfNormalizedDVRUnsection
  exact sfSheafSection_heq T U (normalizedDVRQuotient l E T (Nat.le_succ n))
    (normalizedDVRQuotient l E U (Nat.le_succ n)) M N V W h x

variable {X Z : Scheme.{u}} (j : X ⟶ Z) [IsOpenImmersion j]
  (o : IntegralOpenReduction.Operations l E j)

private def rightSectionComparison (n : ℕ)
    (r : IntegralOpenReduction.finiteRestriction l E j o n ≅
      sfIntrinsicOpenRestriction j (Padic.coefficientExtensionRing l E (n + 1)))
    (N : normalizedDVRModules l E Z n) :
    (SheafOfModules.localizedSystemRestriction.{u + 1, u, u + 1}
      (IntegralOpenReduction.rings l E Z n) (IntegralOpenReduction.openObject j)).obj N ⟶
    (SheafOfModules.pushforward.{u + 1} (F := IntegralOpenReduction.sliceSite j)
      ((sheafCompose _ (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
        (o.finiteMap n))).obj
      ((sfIntrinsicOpenRestriction j (Padic.coefficientExtensionRing l E (n + 1))).obj N) :=
  (o.finite n).counitIso.inv.app _ ≫ (o.finite n).functor.map (r.hom.app N) ≫
    (eqToHom (o.finiteFunctor n)).app _

private theorem eqToHom_section_heq {C D : Type*} [Category C] [Category D]
    {J : GrothendieckTopology D} {R : Sheaf J RingCat.{v}}
    {F G : C ⥤ SheafOfModules.{w} R} (h : F = G)
    (M : C) (V : Dᵒᵖ) (x : (F.obj M).val.obj V) :
    HEq (((eqToHom h).app M).val.app V x) x := by
  cases h
  rfl

private theorem unscalar_section_heq (T : Scheme.{u})
    {R R' S : Sheaf (ProEt.topology T) RingCat.{u + 1}} (φ : R ⟶ S) (ψ : R' ⟶ S)
    (M : SheafOfModules.{u + 1} S) (V : T.ProEtᵒᵖ)
    (x : ((SheafOfModules.restrictScalars φ).obj M).val.obj V)
    (y : ((SheafOfModules.restrictScalars ψ).obj M).val.obj V) (h : HEq x y) :
    sfSheafUnscalarSection T φ M V x = sfSheafUnscalarSection T ψ M V y := by
  unfold sfSheafUnscalarSection
  exact eq_of_heq h

private theorem scalarMap_section (T : Scheme.{u})
    {R S : Sheaf (ProEt.topology T) RingCat.{u + 1}} (φ : R ⟶ S)
    {M N : SheafOfModules.{u + 1} S} (f : M ⟶ N) (V : T.ProEtᵒᵖ) (x : M.val.obj V) :
    HEq (((SheafOfModules.restrictScalars φ).map f).val.app V
      (sfSheafScalarSection T φ M V x)) (f.val.app V x) := by
  unfold sfSheafScalarSection
  rfl

@[irreducible] private def coefficientUnsection (T : Scheme.{u}) {A B : Type u}
    [CommRing A] [CommRing B] (φ : A →+* B)
    (M : proEtaleRingModules T (proEtaleConstantRing T B)) (V : T.ProEtᵒᵖ)
    (x : ((proEtaleCoefficientRestrictScalars T φ).obj M).val.obj V) : M.val.obj V :=
  sfSheafUnscalarSection T
    ((sheafCompose _ (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
      ((constantSheaf (ProEt.topology T) CommRingCat.{u + 1}).map
        (CommRingCat.ofHom φ.ulift))) M V x

private theorem intrinsicGenerator_restriction_unsection {A B : Type u}
    [CommRing A] [CommRing B] [Finite A] [Finite B] (φ : A →+* B)
    (M : proEtaleRingModules X (proEtaleConstantRing X B)) (W : Z.ProEt)
    (a : W ⟶ IntegralOpenReduction.openObject j)
    (x : ((proEtaleCoefficientRestrictScalars X φ).obj M).val.obj
      (op ((IntegralOpenReduction.sliceSite j).obj (Over.mk a)))) :
    HEq (((sfOpenRestriction j φ).hom.app M).val.app (op W)
      (sfOpenUnitGenerator j A ((proEtaleCoefficientRestrictScalars X φ).obj M) W a x))
      (sfOpenUnitGenerator j B M W a (coefficientUnsection X φ M _ x)) := by
  unfold coefficientUnsection sfSheafUnscalarSection
  exact heq_of_eq (sfOpenUnitGenerator_restriction j φ M W a x)

private theorem presentation_section (T : Scheme.{u}) (n : ℕ)
    (M : normalizedDVRModules l E T n) (V : T.ProEtᵒᵖ)
    (x : ((normalizedDVRModuleRes l E T (Nat.le_succ n)).obj M).val.obj V) :
    HEq (((sfFiniteOpenPresentationRestriction l E T n).hom.app M).val.app V x) x := by
  exact eqToHom_section_heq (sfFiniteOpenPresentation_restriction_eq l E T n) M V x

private theorem presentation_unsection (T : Scheme.{u}) (n : ℕ)
    (M : normalizedDVRModules l E T n) (V : T.ProEtᵒᵖ)
    (x : ((normalizedDVRModuleRes l E T (Nat.le_succ n)).obj M).val.obj V) :
    coefficientUnsection T (Padic.coefficientExtensionTransition l E (n + 1)) M V
        (((sfFiniteOpenPresentationRestriction l E T n).hom.app M).val.app V x) =
      sfNormalizedDVRUnsection l E T (Nat.le_succ n) M V x := by
  unfold coefficientUnsection sfNormalizedDVRUnsection
  exact unscalar_section_heq T _ _ M V _ x (presentation_section l E T n M V x)

private theorem rightSectionComparison_evaluate (n : ℕ)
    (r : IntegralOpenReduction.finiteRestriction l E j o n ≅
      sfIntrinsicOpenRestriction j (Padic.coefficientExtensionRing l E (n + 1)))
    (h : SfFiniteOpenRestrictionNormalized l E j o n r)
    (N : normalizedDVRModules l E Z n) (W : Z.ProEt)
    (a : W ⟶ IntegralOpenReduction.openObject j) (y : N.val.obj (op W)) :
    N.val.map (sfFiniteOpenSliceObjectIso j (Over.mk a)).inv.op
      ((((sfOpenGeneratorUnderlying j
        (Padic.coefficientExtensionRing l E (n + 1))).hom.app N).hom.app
        (op ((IntegralOpenReduction.sliceSite j).obj (Over.mk a))))
          ((rightSectionComparison l E j o n r N).val.app (op (Over.mk a)) y)) = y := by
  let A := Padic.coefficientExtensionRing l E (n + 1)
  let V := (IntegralOpenReduction.sliceSite j).obj (Over.mk a)
  let C := (MorphismProperty.Over.map ⊤ (inferInstance : WeaklyEtale j)).obj V
  let e := sfFiniteOpenSliceObjectIso j (Over.mk a)
  obtain ⟨z, rfl⟩ := (ConcreteCategory.bijective_of_isIso (N.val.presheaf.map e.inv.op)).2 y
  obtain ⟨x, rfl⟩ := (ConcreteCategory.bijective_of_isIso
    (((sfOpenGeneratorInverse Z A).hom.app N).hom.app (op C))).2 z
  unfold SfFiniteOpenRestrictionNormalized at h
  have hh := h N (Over.mk a) x
  rw [← sfOpenGeneratorInverse_hom] at hh
  change (rightSectionComparison l E j o n r N).val.app (op (Over.mk a))
    (N.val.map e.inv.op ((((sfOpenGeneratorInverse Z A).hom.app N).hom.app (op C)) x)) =
      (((sfOpenGeneratorRealize X A).hom.app
        ((ProEtale.openImmersionRestriction (ModuleCat.{u + 1} (ULift.{u + 1} A)) j).obj
          ((sfIntrinsicModuleEquivalence Z A).inverse.obj N))).hom.app (op V)) x at hh
  change N.val.map e.inv.op
    ((((sfOpenGeneratorUnderlying j A).hom.app N).hom.app (op V))
      ((rightSectionComparison l E j o n r N).val.app (op (Over.mk a))
        (N.val.map e.inv.op ((((sfOpenGeneratorInverse Z A).hom.app N).hom.app (op C)) x)))) = _
  rw [hh]
  apply congrArg (N.val.map e.inv.op)
  change ((((sfOpenGeneratorInverse Z A).hom.app N).hom.app (op C)))
      (((sfOpenGeneratorRealize X A).inv.app
        ((ProEtale.openImmersionRestriction
          (ModuleCat.{u + 1} (ULift.{u + 1} A)) j).obj
            ((sfIntrinsicModuleEquivalence Z A).inverse.obj N))).hom.app (op V)
        (((sfOpenGeneratorRealize X A).hom.app
          ((ProEtale.openImmersionRestriction
            (ModuleCat.{u + 1} (ULift.{u + 1} A)) j).obj
              ((sfIntrinsicModuleEquivalence Z A).inverse.obj N))).hom.app (op V) x)) = _
  apply congrArg ((((sfOpenGeneratorInverse Z A).hom.app N).hom.app (op C)))
  let F := (ProEtale.openImmersionRestriction
    (ModuleCat.{u + 1} (ULift.{u + 1} A)) j).obj
      ((sfIntrinsicModuleEquivalence Z A).inverse.obj N)
  exact congrArg (fun f ↦ f.hom.app (op V) x)
    ((sfOpenGeneratorRealize X A).app F).hom_inv_id

private theorem leftComparison_generator (n : ℕ)
    (r : IntegralOpenReduction.finiteRestriction l E j o n ≅
      sfIntrinsicOpenRestriction j (Padic.coefficientExtensionRing l E (n + 1)))
    (h : SfFiniteOpenRestrictionNormalized l E j o n r)
    (M : normalizedDVRModules l E X n) (W : Z.ProEt)
    (a : W ⟶ IntegralOpenReduction.openObject j)
    (x : M.val.obj (op ((IntegralOpenReduction.sliceSite j).obj (Over.mk a)))) :
    ((sfFiniteOpenLeftComparison l E j o n r).hom.app M).val.app (op W)
      (IntegralOpenReduction.finiteExtensionSection l E j o n M W a x) =
      sfOpenUnitGenerator j (Padic.coefficientExtensionRing l E (n + 1)) M W a x := by
  let A := Padic.coefficientExtensionRing l E (n + 1)
  let adj := SheafOfModules.localizedSystemAdjunction.{u + 1, u, u + 1}
    (IntegralOpenReduction.rings l E Z n) (IntegralOpenReduction.openObject j)
  let adj' := sfIntrinsicExtensionByZeroAdjunction j A
  let c := ((((o.finite n).toAdjunction.comp adj).ofNatIsoRight r).leftAdjointUniq adj').hom.app M
  let N := (sfIntrinsicExtensionByZero j A).obj M
  let t := eqToIso (o.finiteFunctor n)
  have hc' := sfOpenGeneratorTransportedUnit (o.finite n) adj adj' r t M
  let V := op (Over.mk a)
  let x' := (t.inv.app M).val.app V x
  have hu := (SheafOfModules.localizedSystemAdjunction_existsUnique.{u + 1, u, u + 1}
    (IntegralOpenReduction.rings l E Z n) (IntegralOpenReduction.openObject j)).exists.choose_spec
      ((o.finite n).functor.obj M) V x'
  change (adj.unit.app ((o.finite n).functor.obj M)).val.app V x' =
    IntegralOpenReduction.finiteExtensionSection l E j o n M W a x at hu
  have he := congrArg (fun f ↦ f.val.app V x') hc'
  change (rightSectionComparison l E j o n r N).val.app V
      (c.val.app (op W) ((adj.unit.app ((o.finite n).functor.obj M)).val.app V x')) =
    (adj'.unit.app M).val.app
      (op ((IntegralOpenReduction.sliceSite j).obj (Over.mk a)))
        ((t.hom.app M).val.app V x') at he
  rw [hu] at he
  have ht : (t.hom.app M).val.app V x' = x := by
    exact congrArg (fun f ↦ f.val.app V x) (t.app M).inv_hom_id
  rw [ht] at he
  have he' := congrArg (fun z ↦ N.val.map
    (sfFiniteOpenSliceObjectIso j (Over.mk a)).inv.op
      ((((sfOpenGeneratorUnderlying j A).hom.app N).hom.app
        (op ((IntegralOpenReduction.sliceSite j).obj (Over.mk a)))) z)) he
  have result := (rightSectionComparison_evaluate l E j o n r h N W a
    (c.val.app (op W)
      (IntegralOpenReduction.finiteExtensionSection l E j o n M W a x))).symm.trans he'
  unfold sfFiniteOpenLeftComparison sfFiniteOpenAdjunction
  exact result

/-- The intrinsic side of the adjacent coefficient square, before evaluating sections.
Source: Stacks 0E8I (blueprint: lem-sf-finite-open-coefficient-generators). -/
@[reducible] def sfFiniteOpenIntrinsicCoefficient (n : ℕ)
    (r : IntegralOpenReduction.finiteRestriction l E j o (n + 1) ≅
      sfIntrinsicOpenRestriction j (Padic.coefficientExtensionRing l E (n + 2))) :
    normalizedDVRModuleRes l E X (Nat.le_succ n) ⋙
        IntegralOpenReduction.finiteExtension l E j o (n + 1) ≅
      sfIntrinsicExtensionByZero j (Padic.coefficientExtensionRing l E (n + 1)) ⋙
        sfCompactSupportFiniteRestriction l E Z n :=
  Functor.isoWhiskerLeft (normalizedDVRModuleRes l E X (Nat.le_succ n))
      (sfFiniteOpenLeftComparison l E j o (n + 1) r) ≪≫
    Functor.isoWhiskerRight (sfFiniteOpenPresentationRestriction l E X n)
      (sfIntrinsicExtensionByZero j (Padic.coefficientExtensionRing l E (n + 2))) ≪≫
    sfOpenRestriction j (Padic.coefficientExtensionTransition l E (n + 1))

/-- The target presentation of the lower extension comparison.
Source: Stacks 0E8I (blueprint: lem-sf-finite-open-coefficient-generators). -/
@[reducible] def sfFiniteOpenLowerCoefficient (n : ℕ)
    (r : IntegralOpenReduction.finiteRestriction l E j o n ≅
      sfIntrinsicOpenRestriction j (Padic.coefficientExtensionRing l E (n + 1))) :
    IntegralOpenReduction.finiteExtension l E j o n ⋙
        normalizedDVRModuleRes l E Z (Nat.le_succ n) ≅
      sfIntrinsicExtensionByZero j (Padic.coefficientExtensionRing l E (n + 1)) ⋙
        sfCompactSupportFiniteRestriction l E Z n :=
  Functor.isoWhiskerRight (sfFiniteOpenLeftComparison l E j o n r)
      (normalizedDVRModuleRes l E Z (Nat.le_succ n)) ≪≫
    Functor.isoWhiskerLeft
      (sfIntrinsicExtensionByZero j (Padic.coefficientExtensionRing l E (n + 1)))
      (sfFiniteOpenPresentationRestriction l E Z n)

/-- The intrinsic coefficient comparison preserves a single extension generator.
The two left comparisons are constructed from the supplied, section-normalized
right comparisons. No ordinary slice coefficient comparison is assumed.
Source: Stacks 03DI, 03DJ and 0E8I
(blueprint: lem-sf-finite-open-coefficient-generators).

Proof: apply the intrinsic open restriction to the proposed equality and precompose
with the open adjunction unit. The left-adjoint uniqueness unit equation identifies
the two left comparisons with the supplied right comparisons. Their section
normalizations identify their values with the represented section x. The published
`sfOpenRestriction_normalized_unique` unit equation identifies the coefficient
comparison with the same section, restricted along the quotient ring map. Thus both
sides agree on the indicated generator. The constant units commute with the quotient
map by naturality, and `o.finiteConstants` identifies the scalar actions. The slice
counit and realization counit cancel with their units; the only remaining maps are
the displayed canonical restriction comparison components. This argument is for a
single generator and a single adjacent quotient, before sheafification extensionality;
it uses neither a tower nor a choice of an ordinary coefficient comparison. -/
@[irreducible] def SfFiniteOpenCoefficientGenerator (n : ℕ)
    (r₀ : IntegralOpenReduction.finiteRestriction l E j o n ≅
      sfIntrinsicOpenRestriction j (Padic.coefficientExtensionRing l E (n + 1)))
    (r₁ : IntegralOpenReduction.finiteRestriction l E j o (n + 1) ≅
      sfIntrinsicOpenRestriction j (Padic.coefficientExtensionRing l E (n + 2)))
    (M : normalizedDVRModules l E X n) (W : Z.ProEt)
    (a : W ⟶ IntegralOpenReduction.openObject j)
    : Prop :=
  ∀ x : ((normalizedDVRModuleRes l E X (Nat.le_succ n)).obj M).val.obj
      (op ((IntegralOpenReduction.sliceSite j).obj (Over.mk a))),
    ((sfFiniteOpenIntrinsicCoefficient l E j o n r₁).hom.app M).val.app (op W)
      (IntegralOpenReduction.finiteExtensionSection l E j o (n + 1)
        ((normalizedDVRModuleRes l E X (Nat.le_succ n)).obj M) W a x) =
    ((sfFiniteOpenLowerCoefficient l E j o n r₀).hom.app M).val.app (op W)
      (sfNormalizedDVRSection l E Z (Nat.le_succ n)
        ((IntegralOpenReduction.finiteExtension l E j o n).obj M) (op W)
        (IntegralOpenReduction.finiteExtensionSection l E j o n M W a
          (sfNormalizedDVRUnsection l E X (Nat.le_succ n) M
            (op ((IntegralOpenReduction.sliceSite j).obj (Over.mk a))) x)))

/-- The intrinsic coefficient comparison preserves the represented section function.
Source: Stacks 03DI, 03DJ, 0E8I
(blueprint: lem-sf-finite-open-coefficient-generators).

Proof: the realization unit is invertible on underlying abelian sheaves, so its
inverse and the realization counit identify an intrinsic open-restriction section
with an ambient section. Evaluating the intrinsic adjunction unit this way defines
an intrinsic generator. The supplied right-comparison normalization and the
left-adjoint uniqueness unit equation compute each finite left comparison on its
actual direct-sum generator. Naturality of realization and its sectionwise scalar
normalization show that this evaluation commutes with the coefficient square.
The normalized sfOpenRestriction unit equation therefore preserves the intrinsic
generator. Naturality under the source presentation isomorphism identifies the upper
route, while the lower one-coefficient computation identifies the lower route.
Heterogeneous section identities keep the quotient carriers abstract until both
routes have the same target, when their equality gives the stated result. -/
theorem sfFiniteOpenCoefficient_generator (n : ℕ)
    (r₀ : IntegralOpenReduction.finiteRestriction l E j o n ≅
      sfIntrinsicOpenRestriction j (Padic.coefficientExtensionRing l E (n + 1)))
    (r₁ : IntegralOpenReduction.finiteRestriction l E j o (n + 1) ≅
      sfIntrinsicOpenRestriction j (Padic.coefficientExtensionRing l E (n + 2)))
    (_h₀ : SfFiniteOpenRestrictionNormalized l E j o n r₀)
    (_h₁ : SfFiniteOpenRestrictionNormalized l E j o (n + 1) r₁)
    (M : normalizedDVRModules l E X n) (W : Z.ProEt)
    (a : W ⟶ IntegralOpenReduction.openObject j)
    : SfFiniteOpenCoefficientGenerator l E j o n r₀ r₁ M W a := by
  unfold SfFiniteOpenCoefficientGenerator
  intro x
  let V := op ((IntegralOpenReduction.sliceSite j).obj (Over.mk a))
  let y := sfNormalizedDVRUnsection l E X (Nat.le_succ n) M V x
  have lower :
      HEq (((sfFiniteOpenLowerCoefficient l E j o n r₀).hom.app M).val.app (op W)
        (sfNormalizedDVRSection l E Z (Nat.le_succ n)
          ((IntegralOpenReduction.finiteExtension l E j o n).obj M) (op W)
          (IntegralOpenReduction.finiteExtensionSection l E j o n M W a y)))
        (sfOpenUnitGenerator j (Padic.coefficientExtensionRing l E (n + 1)) M W a y) := by
    let N := (sfIntrinsicExtensionByZero j
      (Padic.coefficientExtensionRing l E (n + 1))).obj M
    let c := (sfFiniteOpenLeftComparison l E j o n r₀).hom.app M
    let q := normalizedDVRModuleRes l E Z (Nat.le_succ n)
    let z := IntegralOpenReduction.finiteExtensionSection l E j o n M W a y
    change HEq (((sfFiniteOpenPresentationRestriction l E Z n).hom.app N).val.app (op W)
      ((q.map c).val.app (op W)
        (sfNormalizedDVRSection l E Z (Nat.le_succ n)
          ((IntegralOpenReduction.finiteExtension l E j o n).obj M) (op W) z))) _
    unfold sfNormalizedDVRSection
    have hp := presentation_section l E Z n N (op W)
      ((q.map c).val.app (op W)
        (sfSheafScalarSection Z (normalizedDVRQuotient l E Z (Nat.le_succ n))
          ((IntegralOpenReduction.finiteExtension l E j o n).obj M) (op W) z))
    have hs := scalarMap_section Z (normalizedDVRQuotient l E Z (Nat.le_succ n))
      c (op W) z
    exact hp.trans (hs.trans (heq_of_eq
      (leftComparison_generator l E j o n r₀ _h₀ M W a y)))
  have upper :
      HEq (((sfFiniteOpenIntrinsicCoefficient l E j o n r₁).hom.app M).val.app (op W)
        (IntegralOpenReduction.finiteExtensionSection l E j o (n + 1)
          ((normalizedDVRModuleRes l E X (Nat.le_succ n)).obj M) W a x))
        (sfOpenUnitGenerator j (Padic.coefficientExtensionRing l E (n + 1)) M W a y) := by
    let A := Padic.coefficientExtensionRing l E (n + 2)
    let M' := (normalizedDVRModuleRes l E X (Nat.le_succ n)).obj M
    let f := (sfFiniteOpenPresentationRestriction l E X n).hom.app M
    let e := (sfOpenRestriction j
      (Padic.coefficientExtensionTransition l E (n + 1))).hom.app M
    change HEq (e.val.app (op W)
      (((sfIntrinsicExtensionByZero j A).map f).val.app (op W)
        (((sfFiniteOpenLeftComparison l E j o (n + 1) r₁).hom.app M').val.app (op W)
          (IntegralOpenReduction.finiteExtensionSection l E j o (n + 1) M' W a x)))) _
    have hl := leftComparison_generator l E j o (n + 1) r₁ _h₁ M' W a x
    refine (heq_of_eq (congrArg (fun z ↦ e.val.app (op W)
      (((sfIntrinsicExtensionByZero j A).map f).val.app (op W) z)) hl)).trans ?_
    have hm := sfOpenUnitGenerator_map j A f W a x
    refine (heq_of_eq (congrArg (e.val.app (op W)) hm)).trans ?_
    refine (intrinsicGenerator_restriction_unsection j
      (Padic.coefficientExtensionTransition l E (n + 1)) M W a _).trans ?_
    exact heq_of_eq (congrArg
      (sfOpenUnitGenerator j (Padic.coefficientExtensionRing l E (n + 1)) M W a)
      (presentation_unsection l E X n M V x))
  exact eq_of_heq (upper.trans lower.symm)

end WeilConjectures
