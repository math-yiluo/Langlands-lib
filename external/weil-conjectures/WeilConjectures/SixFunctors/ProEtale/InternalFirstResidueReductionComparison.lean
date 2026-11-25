/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.IntegralConstantModelRealization
public import WeilConjectures.AlgebraicGeometry.IntegralModelsStacksData
import all WeilConjectures.Algebra.Homology.InternalKFlatScalarTowerRealization
import all WeilConjectures.AlgebraicGeometry.ConstantCompletionCore
import all WeilConjectures.AlgebraicGeometry.IntegralCoefficientSquareNormalization
import all WeilConjectures.CategoryTheory.InternalSectionTensorComparison
import WeilConjectures.SixFunctors.ProEtale.InternalFirstResidueOrdinaryComparison

/-! # The common first quotient in the internal coefficient presentation

Source: integral-models proof (1)--(2), Stacks Tags 099L and 08FZ.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale

attribute [local irreducible] upperStarFromPoint
  IntegralModelsStacks.scalarMap IntegralModelsStacks.residueMap
  IntegralConstantModel.pointComparison
  Sheaf.monoidalCategory Mod.extendScalars Mod.comap
  Functor.mapDerivedCategory Functor.leftDerivedFunctor

local instance firstResidueSiteSmall (X : Scheme.{u}) : EssentiallySmall.{u + 1} X.ProEt :=
  essentiallySmallSelf.{0, u, u + 1} _

local instance firstResidueAbSheafify (X : Scheme.{u}) :
    HasSheafify (Scheme.ProEt.topology X) AddCommGrpCat.{u + 1} :=
  WeilConjectures.integralCoefficientAbSheafify.{u, u} X

local instance firstResidueAbLocallyBijective (X : Scheme.{u}) :
    (Scheme.ProEt.topology X).WEqualsLocallyBijective AddCommGrpCat.{u + 1} :=
  WeilConjectures.integralCoefficientAbLocallyBijective.{u, u} X

/-- Flat scalar restriction preserves native K-flat complexes. The section-action
comparison reduces this to the ordinary sheaf-module flat restriction theorem. -/
private theorem firstResidueRestrictionKFlat
    (X : Scheme.{u})
    {R S : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}}
    [MonObj R] [IsCommMonObj R] [MonObj S] [IsCommMonObj S]
    (a : R ⟶ S) [IsMonHom a] [PreservesFiniteLimits (Mod.extendScalars a)]
    (P : CochainComplex (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) S) ℤ)
    (hP : (HomologicalComplex.quasiIso _ (.up ℤ)).kFlat P) :
    (HomologicalComplex.quasiIso _ (.up ℤ)).kFlat
      (((Mod.comap a).mapHomologicalComplex (.up ℤ)).obj P) := by
  let J := Scheme.ProEt.topology X
  let eS := InternalAbelianSheafModule.sectionModuleEquivalence J S
  have hB := IntegralCoefficientSquare.flat_restricted_regular X a
  have hK := (InternalAbelianSheafModule.comparison_kflat J S P).mp
    ((IntegralCoefficientSquare.internal_kflat_iff P).mpr hP)
  let α := CondensedRing.sectionRingMap X a
  let U := SheafOfModules.restrictScalars
    ((sheafCompose J (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map α)
  let β := CondensedRing.sectionModuleComapIso X a
  let b := β.app (Mod.regular S) ≪≫ U.mapIso (CondensedRing.sectionModuleRegularIso X S)
  have hb := SheafOfModules.flatOnSite_of_iso _ b hB
  have h := SheafOfModules.isKFlat_restrictScalars_of_flat α hb
    ((eS.functor.mapHomologicalComplex (.up ℤ)).obj P) hK
  let d := (NatIso.mapHomologicalComplex β (.up ℤ)).app P
  exact (IntegralCoefficientSquare.internal_kflat_iff _).mp
    ((InternalAbelianSheafModule.comparison_kflat J R _).mpr
      (SheafOfModules.kFlat_iso_independent _ d.symm h.1))

/-- Derive an ordinary common-quotient square using one native K-flat resolution. -/
private theorem firstResidueDerivedSquare
    (X : Scheme.{u})
    {R S T V : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}}
    [MonObj R] [IsCommMonObj R] [MonObj S] [IsCommMonObj S]
    [MonObj T] [IsCommMonObj T] [MonObj V] [IsCommMonObj V]
    (a : R ⟶ S) [IsMonHom a] [PreservesFiniteLimits (Mod.extendScalars a)]
    (q : R ⟶ T) [IsMonHom q] (p : S ⟶ V) [IsMonHom p]
    (i : T ⟶ V) [IsMonHom i]
    (γ : Mod.comap a ⋙ Mod.extendScalars q ≅ Mod.extendScalars p ⋙ Mod.comap i) :
    Nonempty
      ((Mod.comap a).mapDerivedCategory ⋙ (Mod.extendScalars q).leftDerivedFunctor ≅
        (Mod.extendScalars p).leftDerivedFunctor ⋙ (Mod.comap i).mapDerivedCategory) := by
  let r := Mod.comap (D := Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) a
  let f := Mod.extendScalars q
  let b := Mod.extendScalars p
  let t := Mod.comap (D := Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) i
  let P : CochainComplex (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) S) ℤ → Prop :=
    fun K ↦ (HomologicalComplex.quasiIso _ (.up ℤ)).kFlat K
  have hres (K : CochainComplex (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) S) ℤ) :
      ∃ (L : CochainComplex (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) S) ℤ)
        (z : L ⟶ K), P L ∧ QuasiIso z := by
    obtain ⟨L, z, hz, _, hL⟩ := CochainComplex.exists_quasiIso_flat_kFlat K
    exact ⟨L, z, hL, hz⟩
  obtain ⟨d, _, _⟩ := ConstantCompletion.resolving_square_iso
    DerivedCategory.Q DerivedCategory.Q DerivedCategory.Q
    (r.mapHomologicalComplex (.up ℤ)) (b.mapHomologicalComplex (.up ℤ))
    (f.mapHomologicalComplex (.up ℤ)) (t.mapHomologicalComplex (.up ℤ))
    r.mapDerivedCategory b.leftDerivedFunctor f.leftDerivedFunctor t.mapDerivedCategory
    r.mapDerivedCategoryFactors.hom (Mod.KFlatScalarTower.computationCounit q)
    (NatIso.mapHomologicalComplex γ (.up ℤ))
    (Mod.KFlatScalarTower.computationCounit p) t.mapDerivedCategoryFactors.hom P hres
    (fun _ _ ↦ inferInstance)
    (fun K hK ↦ by
      have := f.isIso_leftDerivedFunctorCounit_app_of_kFlat _
        (firstResidueRestrictionKFlat X a K hK)
      dsimp only [Mod.KFlatScalarTower.computationCounit, NatTrans.comp_app,
        Functor.whiskerRight_app, Functor.whiskerLeft_app]
      infer_instance)
    (fun K hK ↦ by
      have := b.isIso_leftDerivedFunctorCounit_app_of_kFlat K hK
      dsimp only [Mod.KFlatScalarTower.computationCounit, NatTrans.comp_app,
        Functor.whiskerRight_app, Functor.whiskerLeft_app]
      infer_instance)
    (fun _ _ ↦ inferInstance)
  exact ⟨d⟩

/-- Exact restriction commutes with composition on derived categories. -/
private def firstResidueRestrictionComp
    (X : Scheme.{u}) {R S T : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}}
    [MonObj R] [MonObj S] [MonObj T]
    (f : R ⟶ S) [IsMonHom f] (g : S ⟶ T) [IsMonHom g] :
    (Mod.comap (D := Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) g).mapDerivedCategory ⋙
        (Mod.comap (D := Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) f).mapDerivedCategory ≅
      (Mod.comap (D := Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (f ≫ g)).mapDerivedCategory :=
  (Functor.mapDerivedCategoryCompIso
    (Mod.comap (D := Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) g)
    (Mod.comap (D := Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) f)) ≪≫
    Functor.mapDerivedCategoryNatIso (Mod.comapComp f g).symm

attribute [local irreducible] firstResidueRestrictionComp

private def firstResidueComposeSquare
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    (F : A ⥤ B) (G : B ⥤ C) (H : C ⥤ D) (R : A ⥤ C) (T : A ⥤ D)
    (c : F ⋙ G ≅ R) (d : R ⋙ H ≅ T) : F ⋙ G ⋙ H ≅ T :=
  (Functor.associator F G H).symm ≪≫ Functor.isoWhiskerRight c H ≪≫ d

/-- Two exact restrictions followed by residue extension compute the same square. -/
private theorem firstResidueTwoRestrictionSquare
    (X : Scheme.{u})
    {R S B T V : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}}
    [MonObj R] [IsCommMonObj R] [MonObj S] [IsCommMonObj S]
    [MonObj B] [IsCommMonObj B] [MonObj T] [IsCommMonObj T]
    [MonObj V] [IsCommMonObj V]
    (f : R ⟶ S) [IsMonHom f] (g : S ⟶ B) [IsMonHom g]
    [PreservesFiniteLimits (Mod.extendScalars (f ≫ g))]
    (q : R ⟶ T) [IsMonHom q] (p : B ⟶ V) [IsMonHom p]
    (i : T ⟶ V) [IsMonHom i]
    (γ : Mod.comap (f ≫ g) ⋙ Mod.extendScalars q ≅
      Mod.extendScalars p ⋙ Mod.comap i) :
    Nonempty
      ((Mod.comap g).mapDerivedCategory ⋙ (Mod.comap f).mapDerivedCategory ⋙
          (Mod.extendScalars q).leftDerivedFunctor ≅
        (Mod.extendScalars p).leftDerivedFunctor ⋙ (Mod.comap i).mapDerivedCategory) := by
  obtain ⟨d⟩ := firstResidueDerivedSquare X (f ≫ g) q p i γ
  let c := firstResidueRestrictionComp X f g
  exact ⟨firstResidueComposeSquare _ _ _ _ _ c d⟩

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
  WeilConjectures.integralCoefficientAbLocallyBijective
  WeilConjectures.integralCoefficientAbSheafify WeilConjectures.integralCoefficientRingSheafify in
/-- The two first derived residue functors are naturally isomorphic after a residue
coefficient isomorphism. There is no finiteness condition on the scheme or on the input complex.
Source: integral-models proof (1)--(2), Stacks Tags 099L and 08FZ.
(auxiliary; not a blueprint node).

Proof: put A = O_E and k = A/(pi). The constant-to-continuous map on k is an
isomorphism: a continuous function to the finite discrete ring k is constant on the
finite clopen cover by its fibres; equality of two constants is also detected on this
cover, including the empty cover. Sheafification therefore identifies both ring objects,
with their pointwise operations. Use the inverse of this map for e. The square of
constant-to-continuous maps for A and k commutes by evaluation on constant sections.
The integral map is flat and induces the common quotient isomorphism, by the integral
constant completion theorem. On a flat-term K-flat representative P, restricting P
along this flat map leaves a K-flat complex: tensoring with an acyclic A-complex is
identified with tensoring P with its exact extension to the continuous ring. The
common-quotient tensor comparison sends s tensor p to s tensor p and is invertible,
as follows either from the quotient isomorphism and flatness or the normalized
finite-reduction comparison in integral_constant_completion. Exact section-action and
small-site equivalences carry that comparison back to internal modules; the inverse
pointComparison reconciles the two equal integral point presentations. All maps are
natural in P and commute with differentials and quasi-isomorphisms. The universal
property of localization gives the displayed natural isomorphism for unbounded derived
categories. No choice of a complete representative, cohomological bound, or
constructible local model enters this construction. The empty scheme and zero complex
satisfy the same tensor identities. -/
theorem internal_first_residue_reduction_comparison
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] (X : Scheme.{u}) :
    ∃ e : Mon.mk (DerivedNakayama.quotientRing l E 1) ≅
        Mon.mk (IntegralModelsStacks.discreteObj (Padic.coefficientExtensionRing l E 1)),
      Nonempty
        ((Mod.comap (coefficientMap
            (IntegralConstantModel.pointComparison l E).inv.hom X)).mapDerivedCategory ⋙
          IntegralModelsStacks.restriction l E X ⋙
          (Mod.extendScalars (IntegralModelsStacks.residueMap l E X)).leftDerivedFunctor ≅
        AdicCompletion.derivedReduction l E X 0 ⋙
          (Mod.comap (coefficientMap e.inv.hom X)).mapDerivedCategory) := by
  obtain ⟨e, hflat, ⟨γ⟩⟩ := internal_first_residue_ordinary_comparison l E X
  let := hflat
  refine ⟨e, ?_⟩
  exact firstResidueTwoRestrictionSquare X (IntegralModelsStacks.scalarMap l E X)
    (coefficientMap (IntegralConstantModel.pointComparison l E).inv.hom X)
    (IntegralModelsStacks.residueMap l E X) (AdicCompletion.quotient l E X 0)
    (coefficientMap e.inv.hom X) γ

end AlgebraicGeometry.ProEtale
