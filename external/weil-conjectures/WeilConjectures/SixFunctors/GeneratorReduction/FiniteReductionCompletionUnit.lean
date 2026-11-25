/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.IntegralSystemRealization.Canonical.IntegralSystemCanonicalBridge
import all WeilConjectures.SmoothPurity.Integral.IntegralOperationRoosEffectivity
import all WeilConjectures.SmoothPurity.IntegralOnSlice.IntegralDerivedOperationsOnSlices
import all WeilConjectures.TraceFormula.CompletionUnit.CompletionUnitFiniteMateComparison
/-! # Finite reduction of the actual completion unit

Source: current blueprint fix-prop-coherence, primitive comparisons
(blueprint: lem-sf-finite-reduction-completion-unit).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genSizeOfSpec false
set_option genInjectivity false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
open WeilConjectures

namespace WeilConjectures.GeneratorReduction
attribute [local irreducible] scalarReductionExistence scalarReductionDerivedExistence
  completedIntegralCoefficientSheafUnrestricted constantSheaf IntegralOnSlice.roosUnit
attribute [local implicit_reducible] IntegralOnSlice.Site IntegralOnSlice.siteCategory
  IntegralOnSlice.topology IntegralOnSlice.ring IntegralOnSlice.restrict
  IntegralOnSlice.hasDerived scalarReductionSourceDerived integralOperationsRoos
attribute [local irreducible] HasDerivedCategory.standard
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

private instance globalModuleAbelian (X : Scheme.{u}) :
    Abelian (IntegralOnSlice.Mod l E X none) :=
  inferInstanceAs (Abelian (scalarReductionSource l E X))

private theorem roosUnit_coordinate (X : Scheme.{u})
    (P : IntegralOnSlice.Cx l E X none) (n : ℕ) :
    IntegralOnSlice.roosUnit l E X none P ≫
        (CochainComplex.mappingCocone.fst
          (towerTransitionEndomorphism
            (K := fun m ↦ ((IntegralOnSlice.tower l E X none).obj P).obj (op m))
            (integralOperationsTowerStep ((IntegralOnSlice.tower l E X none).obj P))) ≫
          Pi.π (fun m ↦ ((IntegralOnSlice.tower l E X none).obj P).obj (op m)) n) =
      ((IntegralOnSlice.augmentation l E X none).app P).app (op n) := by
  rw [IntegralOnSlice.roosUnit_eq, ← Category.assoc,
    CochainComplex.mappingCocone.lift_fst]
  exact Pi.lift_comp_π _ _

private theorem roosUnit_projection (X : Scheme.{u})
    (P : CochainComplex (scalarReductionSource l E X) ℤ) (n : ℕ) :
    DerivedCategory.Q.map (IntegralOnSlice.roosUnit l E X none P) ≫
        integralOperationRoosProjection l E X
          ((IntegralOnSlice.tower l E X none).obj P) n =
      DerivedCategory.Q.map
        ((((scalarReductionExtension_adjunction l E X n).choose).mapHomologicalComplex
          (.up ℤ)).unit.app P) := by
  let T : ℕᵒᵖ ⥤ CochainComplex (scalarReductionSource l E X) ℤ :=
    (IntegralOnSlice.tower l E X none).obj P
  let F := ((scalarReductionExtension l E X n).mapHomologicalComplex (.up ℤ)).obj P
  let a : P ⟶ integralOperationsRoos T := IntegralOnSlice.roosUnit l E X none P
  let p : integralOperationsRoos T ⟶ T.obj (op n) :=
    CochainComplex.mappingCocone.fst
      (towerTransitionEndomorphism (K := fun m ↦ T.obj (op m))
        (integralOperationsTowerStep T)) ≫ Pi.π (fun m ↦ T.obj (op m)) n
  let γ : P ⟶ ((scalarReductionRestriction l E X n).mapHomologicalComplex (.up ℤ)).obj F :=
    ((IntegralOnSlice.augmentation l E X none).app P).app (op n)
  have hγ : γ =
      ((((scalarReductionExtension_adjunction l E X n).choose).mapHomologicalComplex
        (.up ℤ)).unit.app P) := by
    ext i V x
    exact ((IntegralOnSlice.augmentation_existsUnique l E X none).exists.choose_spec
      P n i V x).trans ((scalarReductionExtension_adjunction l E X n).choose_spec
        (P.X i) V x).symm
  have h : a ≫ p = γ := roosUnit_coordinate l E X P n
  exact (DerivedCategory.Q.map_comp a p).symm.trans
    (congrArg DerivedCategory.Q.map (h.trans hγ))

private theorem finiteExtension_iso_of_projection
    {C D : Type*} [Category* C] [Category* D] {L : C ⥤ D} {R : D ⥤ C}
    (adj : L ⊣ R) {A B N : C} {M : D} (a : A ⟶ B) (p : B ⟶ N)
    (s : R.obj M ≅ N) (c : L.obj A ≅ M)
    (h : a ≫ p = adj.unit.app A ≫ R.map c.hom ≫ s.hom)
    (hi : IsIso ((adj.homEquiv B M).symm (p ≫ s.inv))) : IsIso (L.map a) := by
  have hu : a ≫ (p ≫ s.inv) = adj.unit.app A ≫ R.map c.hom := by
    rw [← Category.assoc, h]
    simp only [Category.assoc, s.hom_inv_id, Category.comp_id]
  have hc : L.map a ≫ (adj.homEquiv B M).symm (p ≫ s.inv) = c.hom := by
    rw [← adj.homEquiv_naturality_left_symm, hu]
    exact (adj.homEquiv A M).symm_apply_apply c.hom
  have : IsIso (L.map a ≫ (adj.homEquiv B M).symm (p ≫ s.inv)) := by
    rw [hc]
    infer_instance
  exact IsIso.of_isIso_comp_right _ ((adj.homEquiv B M).symm (p ≫ s.inv))

private theorem finiteReduction_roosUnit (X : Scheme.{u})
    (P : (integralOperationsGoodComplex l E X).FullSubcategory) (n : ℕ) :
    IsIso ((coefficientFiniteDerivedExtension l E X n).map
      (DerivedCategory.Q.map (IntegralOnSlice.roosUnit l E X none P.obj))) := by
  let Q : CochainComplex (scalarReductionSource l E X) ℤ := P.obj
  let T : ℕᵒᵖ ⥤ CochainComplex (scalarReductionSource l E X) ℤ :=
    (IntegralOnSlice.tower l E X none).obj Q
  let F := fun k : ℕ ↦
    ((scalarReductionExtension l E X k).mapHomologicalComplex (.up ℤ)).obj Q
  let j (k : ℕ) : T.obj (op k) ≅
      ((scalarReductionRestriction l E X k).mapHomologicalComplex (.up ℤ)).obj (F k) :=
    Iso.refl _
  have H := fromOrdinary l E X Q P.property T F (Iso.refl _) j
    (DerivedCategory.Q.obj (integralOperationsRoos T)) (Iso.refl _)
  let adj := coefficientFiniteAdjunction l E X n
  let R := coefficientFiniteDerivedRestriction l E X n
  let p : DerivedCategory.Q.obj (integralOperationsRoos T) ⟶
      DerivedCategory.Q.obj (T.obj (op n)) := integralOperationRoosProjection l E X T n
  let s : R.obj (DerivedCategory.Q.obj (F n)) ≅ DerivedCategory.Q.obj (T.obj (op n)) :=
    (scalarReductionRestriction l E X n).mapDerivedCategoryFactors.app (F n)
  have hi : IsIso ((adj.homEquiv _ _).symm (p ≫ s.inv)) := by
    have h := adjointDropIdentity adj DerivedCategory.Q
      (DerivedCategory.Q.obj (integralOperationsRoos T)) _ (T.obj (op n))
      (DerivedCategory.Q.obj (F n)) (𝟙 _) p s.inv (H.2 n)
    simpa only [Category.id_comp] using h
  let c := coefficientFiniteReductionModel l E X Q P.property.1 n
  let a₀ : Q ⟶ integralOperationsRoos T := IntegralOnSlice.roosUnit l E X none Q
  let a := DerivedCategory.Q.map a₀
  have h : a ≫ p = adj.unit.app (DerivedCategory.Q.obj Q) ≫ R.map c.hom ≫ s.hom :=
    (roosUnit_projection l E X Q n).trans
      (CompletionUnit.finiteModel_unit l E X Q P.property.1 n).symm
  exact finiteExtension_iso_of_projection adj a p s c h hi

/-- Every finite scalar extension inverts the actual quotient-completion unit.
Source: Stacks 099M, 099N and 0941; Bhatt--Scholze, Lemmas 3.5.4--3.5.7.

Proof: choose a flat-term K-flat representative P of K. Its strict quotient tower
is normalized: two successive quotients identify with the smaller quotient by
multiplication of scalars, compatibly with all quotient transitions. The Roos
finite-reduction effectivity theorem identifies the adjoint of the nth Roos
projection with an isomorphism onto the nth quotient of P. The actual quotient
augmentation has first coordinates x mapped to 1 tensor x and shifted coordinate
zero. Therefore the composite of its nth scalar extension with this projection
adjoint is the identity of the nth quotient, by the tensor-restriction triangle
identity. Since the projection adjoint is invertible, the nth scalar extension
of the augmentation is invertible. The characterizing equation of completionUnit
identifies this augmentation after Q, and naturality transports the assertion
along the representative isomorphism to K. There is no completeness assumption
on K; the zero object and every positive quotient exponent are included.
(blueprint: lem-sf-finite-reduction-completion-unit). -/
theorem finiteReduction_completionUnit (X : Scheme.{u})
    (K : DerivedCategory (scalarReductionSource l E X)) (n : ℕ) :
    IsIso ((coefficientFiniteDerivedExtension l E X n).map
      ((IntegralOnSlice.completionUnit l E X none).app K)) := by
  let G : DerivedCategory (scalarReductionSource l E X) ⥤
      DerivedCategory (scalarReductionSource l E X) := IntegralOnSlice.completion l E X none
  let η : 𝟭 (DerivedCategory (scalarReductionSource l E X)) ⟶ G :=
    IntegralOnSlice.completionUnit l E X none
  let q : (IntegralOnSlice.Good l E X none).FullSubcategory ⥤
      DerivedCategory (scalarReductionSource l E X) := IntegralOnSlice.qGood l E X none
  let : q.IsLocalization
      ((HomologicalComplex.quasiIso (IntegralOnSlice.Mod l E X none) (.up ℤ)).inverseImage
        (IntegralOnSlice.Good l E X none).ι) := IntegralOnSlice.goodLocalization l E X none
  let := Localization.essSurj q
    ((HomologicalComplex.quasiIso (IntegralOnSlice.Mod l E X none) (.up ℤ)).inverseImage
      (IntegralOnSlice.Good l E X none).ι)
  let P := q.objPreimage K
  let Q : CochainComplex (scalarReductionSource l E X) ℤ := P.obj
  let e : DerivedCategory.Q.obj Q ≅ K := q.objObjPreimageIso K
  let L := coefficientFiniteDerivedExtension l E X n
  have hP : IsIso (L.map (η.app (DerivedCategory.Q.obj Q))) := by
    let T : ℕᵒᵖ ⥤ CochainComplex (scalarReductionSource l E X) ℤ :=
      (IntegralOnSlice.tower l E X none).obj Q
    let c : G.obj (DerivedCategory.Q.obj Q) ≅
        DerivedCategory.Q.obj (integralOperationsRoos T) :=
      (IntegralOnSlice.completionComparison l E X none).app P
    have h := finiteReduction_roosUnit l E X ⟨Q, P.property⟩ n
    have hu : η.app (DerivedCategory.Q.obj Q) ≫ c.hom =
        DerivedCategory.Q.map (IntegralOnSlice.roosUnit l E X none Q) :=
      (IntegralOnSlice.completionUnit_existsUnique l E X none).exists.choose_spec P
    have hi : IsIso (L.map (η.app (DerivedCategory.Q.obj Q)) ≫ L.map c.hom) := by
      rw [← L.map_comp, hu]
      exact h
    exact IsIso.of_isIso_comp_right _ (L.map c.hom)
  have hn := congrArg L.map (η.naturality e.hom)
  simp only [Functor.id_map, Functor.map_comp] at hn
  have : IsIso (L.map e.hom ≫ L.map (η.app K)) := by
    rw [hn]
    infer_instance
  exact IsIso.of_isIso_comp_left (L.map e.hom) _

end WeilConjectures.GeneratorReduction
