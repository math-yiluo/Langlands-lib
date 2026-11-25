/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.WeilSheaf.Native.NativeCondensedRealizationSheafTensor
public import WeilConjectures.WeilSheaf.Native.Open.NativeOpenTensorNormalizedRestrictionDescent
public import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.Dualizable
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Monoidal

/-!
# Representative models for the derived condensed realization of the native tensor

The inputs of the generic restriction descent
`NativeRestrictionDescentProof.restriction_derived_representative` for the condensed realization
`R = condensedRealization k₀ l X` of pro-étale Weil sheaves:

* `AlgebraicGeometry.ProEtaleWeilSheaf.CondensedIsKFlat`: K-flatness of complexes of condensed
  module objects on the geometric fibre.
* `AlgebraicGeometry.ProEtaleWeilSheaf.condensedTensorModel`: the condensed K-flat model
  `Q P ⊗ᴸ Q T ≅ Q (P ⊗ T)`, the lax monoidal structure of `DerivedCategory.Q`, invertible on
  K-flat complexes (`DerivedCategory.isIso_μ_Q_of_kFlat`), and its naturality
  (`AlgebraicGeometry.ProEtaleWeilSheaf.condensedTensorModel_naturality`).
* `AlgebraicGeometry.ProEtaleWeilSheaf.condensedRealizationTensorInput` and
  `AlgebraicGeometry.ProEtaleWeilSheaf.condensedRealizationTensorModels`: the descent input
  (native and condensed tensors) and its models, with sheaf comparison
  `condensedRealizationSheafTensorIso`.
-/

@[expose] public noncomputable section

universe v u

open CategoryTheory MonoidalCategory Limits ZeroObject

open scoped CategoryTheory.Obj

namespace DerivedCategory

variable {A : Type u} [Category.{v} A] [Abelian A] [IsGrothendieckAbelian.{v} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [MonoidalClosed A] [BraidedCategory A]
  [HasDerivedCategory.{v} A] [Abelian.HasFunctorialFlatResolution A]

/-- The lax monoidal structure `Q P ⊗ᴸ Q T ⟶ Q (P ⊗ T)` of the localization functor
`Q : C(A) ⥤ D(A)` is an isomorphism when `P` is K-flat. -/
lemma isIso_μ_Q_of_kFlat (P T : CochainComplex A ℤ)
    (hP : (HomotopyCategory.quasiIso A (.up ℤ)).kFlat
      ((HomotopyCategory.quotient A (.up ℤ)).obj P)) :
    IsIso (Functor.LaxMonoidal.μ (Q (C := A)) P T) := by
  have := isIso_μ_Qh_of_kFlat _ ((HomotopyCategory.quotient A (.up ℤ)).obj T) hP
  let e := quotientCompQhIso A
  change IsIso ((e.inv.app P ⊗ₘ e.inv.app T) ≫
    (Functor.LaxMonoidal.μ Qh ((HomotopyCategory.quotient A (.up ℤ)).obj P)
      ((HomotopyCategory.quotient A (.up ℤ)).obj T) ≫
      Qh.map (Functor.LaxMonoidal.μ (HomotopyCategory.quotient A (.up ℤ)) P T)) ≫
        e.hom.app (P ⊗ T))
  infer_instance

end DerivedCategory

namespace CategoryTheory.Functor

variable {A B : Type*} [Category* A] [Category* B] [Preadditive A] [Preadditive B]
  (R : B ⥤ A) [R.Additive] [PreservesColimitsOfSize.{0, 0} R]
  (F : A ⥤ A ⥤ A) (G : B ⥤ B ⥤ B)
  [F.PreservesZeroMorphisms] [∀ M, (F.obj M).PreservesZeroMorphisms]
  [G.PreservesZeroMorphisms] [∀ M, (G.obj M).PreservesZeroMorphisms]
  [∀ P T : CochainComplex A ℤ, HomologicalComplex.HasMapBifunctor P T F (.up ℤ)]
  [∀ P T : CochainComplex B ℤ, HomologicalComplex.HasMapBifunctor P T G (.up ℤ)]

/-- The natural transformation of curried bifunctors underlying an isomorphism
`uncurry G ⋙ R ≅ R × R ⋙ uncurry F`. -/
@[simps]
def postcompose₂NatTransOfUncurryIso (r : uncurry.obj G ⋙ R ≅ R.prod R ⋙ uncurry.obj F) :
    (postcompose₂.obj R).obj G ⟶ (((whiskeringLeft₂ A).obj R).obj R).obj F where
  app M :=
    { app N := r.hom.app (M, N)
      naturality N N' b := by
        simpa using r.hom.naturality (Prod.mkHom (𝟙 M) b) }
  naturality M M' a := by
    ext N
    simpa using r.hom.naturality (Prod.mkHom a (𝟙 N))

/-- The totalization of an isomorphism `r : uncurry G ⋙ R ≅ R × R ⋙ uncurry F` comparing two
bifunctors through an additive functor `R` preserving countable coproducts: the isomorphism of
total complexes `R (P ⊗_G T) ≅ R P ⊗_F R T`, induced by `r` on each summand
(`HomologicalComplex.mapBifunctorComparison`). -/
noncomputable def uncurryMap₂CochainComplexIso
    (r : uncurry.obj G ⋙ R ≅ R.prod R ⋙ uncurry.obj F) :
    uncurry.obj G.map₂CochainComplex ⋙ R.mapHomologicalComplex (.up ℤ) ≅
      (R.mapHomologicalComplex (.up ℤ)).prod (R.mapHomologicalComplex (.up ℤ)) ⋙
        uncurry.obj F.map₂CochainComplex :=
  have (M : B) (N : B) : IsIso (((postcompose₂NatTransOfUncurryIso R F G r).app M).app N) :=
    inferInstanceAs (IsIso (r.hom.app (M, N)))
  NatIso.ofComponents
    (fun PT ↦ asIso (HomologicalComplex.mapBifunctorComparison
      (postcompose₂NatTransOfUncurryIso R F G r) (.up ℤ) PT.1 PT.2))
    (fun {PT PT'} fg ↦ by
      dsimp only [comp_map, uncurry_obj_map, prod_map, prod_obj, asIso_hom]
      rw [NativeRestrictionDescentProof.map₂CochainComplex_map_comp_map,
        NativeRestrictionDescentProof.map₂CochainComplex_map_comp_map]
      exact HomologicalComplex.mapBifunctorComparison_naturality _ (.up ℤ) fg.1 fg.2)

/-- On each summand, the totalization `uncurryMap₂CochainComplexIso` is the given comparison
followed by the summand insertion. -/
@[reassoc]
lemma map_ιMapBifunctor_uncurryMap₂CochainComplexIso_hom_app_f
    (r : uncurry.obj G ⋙ R ≅ R.prod R ⋙ uncurry.obj F) (P T : CochainComplex B ℤ)
    (p q n : ℤ) (h : p + q = n) :
    R.map (HomologicalComplex.ιMapBifunctor P T G (.up ℤ) p q n h) ≫
        ((uncurryMap₂CochainComplexIso R F G r).hom.app (P, T)).f n =
      (r.hom.app (P.X p, T.X q)) ≫ HomologicalComplex.ιMapBifunctor
        ((R.mapHomologicalComplex (.up ℤ)).obj P) ((R.mapHomologicalComplex (.up ℤ)).obj T)
        F (.up ℤ) p q n h :=
  HomologicalComplex.map_ιMapBifunctor_mapBifunctorComparisonX _ (.up ℤ) P T p q n h

end CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtaleWeilSheaf

open ProEtale

variable (k₀ : Type u) [Field k₀] [Finite k₀] (l : ℕ) [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]
  (X : Scheme.{u}) [X.Over (Spec (CommRingCat.of k₀))]

/-- The condensed realization preserves small colimits: forgetting the Weil structure creates
them, and the condensed model is an equivalence. -/
instance preservesColimitsOfSize_condensedRealization :
    PreservesColimitsOfSize.{0, 0} (condensedRealization k₀ l X) where
  preservesColimitsOfShape {J} _ := by
    have : HasColimitsOfSize.{0, 0} (AdicSheaf l (X ↘ Spec (CommRingCat.of k₀)).geometricFiber) :=
      hasColimitsOfSizeShrink _
    infer_instance

/-- The K-flat predicate on complexes of condensed module objects on the geometric fibre: the
image in the homotopy category is K-flat. -/
abbrev CondensedIsKFlat (P : CochainComplex (Mod (Sheaf (Scheme.ProEt.topology
    (X ↘ Spec (CommRingCat.of k₀)).geometricFiber) Ab.{u + 1})
    (condensedRingObj (Profinite.padicAlgClRingObj l)
      (X ↘ Spec (CommRingCat.of k₀)).geometricFiber)) ℤ) : Prop :=
  (HomotopyCategory.quasiIso _ (.up ℤ)).kFlat ((HomotopyCategory.quotient _ (.up ℤ)).obj P)

/-- The condensed K-flat model: on K-flat complexes `P`, `T` of condensed module objects, the
lax monoidal structure `Q P ⊗ᴸ Q T ≅ Q (P ⊗ T)` of the localization functor, with `P ⊗ T` the
total tensor complex `(curriedTensor _).map₂CochainComplex`. -/
def condensedTensorModel (P T : CochainComplex (Mod (Sheaf (Scheme.ProEt.topology
    (X ↘ Spec (CommRingCat.of k₀)).geometricFiber) Ab.{u + 1})
    (condensedRingObj (Profinite.padicAlgClRingObj l)
      (X ↘ Spec (CommRingCat.of k₀)).geometricFiber)) ℤ)
    (hP : CondensedIsKFlat k₀ l X P) (_hT : CondensedIsKFlat k₀ l X T) :
    (Functor.uncurry.obj (curriedTensor _)).obj (DerivedCategory.Q.obj P, DerivedCategory.Q.obj T) ≅
      DerivedCategory.Q.obj (((curriedTensor _).map₂CochainComplex.obj P).obj T) :=
  have := DerivedCategory.isIso_μ_Q_of_kFlat P T hP
  asIso (Functor.LaxMonoidal.μ DerivedCategory.Q P T)

omit [Finite k₀] [Fact (ringChar k₀ ≠ l)] in
/-- The condensed K-flat model is natural in both complexes. -/
lemma condensedTensorModel_naturality
    (P P' T T' : CochainComplex (Mod (Sheaf (Scheme.ProEt.topology
    (X ↘ Spec (CommRingCat.of k₀)).geometricFiber) Ab.{u + 1})
    (condensedRingObj (Profinite.padicAlgClRingObj l)
      (X ↘ Spec (CommRingCat.of k₀)).geometricFiber)) ℤ)
    (hP : CondensedIsKFlat k₀ l X P) (hP' : CondensedIsKFlat k₀ l X P')
    (hT : CondensedIsKFlat k₀ l X T) (hT' : CondensedIsKFlat k₀ l X T')
    (f : P ⟶ P') (g : T ⟶ T') :
    (Functor.uncurry.obj (curriedTensor _)).map
        (Prod.mkHom (DerivedCategory.Q.map f) (DerivedCategory.Q.map g)) ≫
        (condensedTensorModel k₀ l X P' T' hP' hT').hom =
      (condensedTensorModel k₀ l X P T hP hT).hom ≫ DerivedCategory.Q.map
        ((((curriedTensor _).map₂CochainComplex).map f).app T ≫
          (((curriedTensor _).map₂CochainComplex).obj P').map g) := by
  have h := Functor.LaxMonoidal.μ_natural DerivedCategory.Q f g
  rw [MonoidalCategory.tensorHom_def] at h
  rw [NativeRestrictionDescentProof.map₂CochainComplex_map_comp_map]
  exact h

variable [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]
  [QuasiCompact (X ↘ Spec (CommRingCat.of k₀))] [IsSeparated (X ↘ Spec (CommRingCat.of k₀))]

/-- The input of the generic restriction descent for the condensed realization: the native
sheaf, total and derived tensors of pro-étale Weil sheaves with the native K-flat predicate, and
the monoidal tensor, its total complex and the derived tensor of condensed module objects with
the K-flat predicate. No extension functor is involved; the zero functor fills that field. -/
def condensedRealizationTensorInput :
    OpenTensorDescentInput (Mod (Sheaf (Scheme.ProEt.topology
      (X ↘ Spec (CommRingCat.of k₀)).geometricFiber) Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj l)
        (X ↘ Spec (CommRingCat.of k₀)).geometricFiber)) (ProEtaleWeilSheaf k₀ l X) :=
  have hE : IsZero ((Functor.const (Mod (Sheaf (Scheme.ProEt.topology
      (X ↘ Spec (CommRingCat.of k₀)).geometricFiber) Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj l)
        (X ↘ Spec (CommRingCat.of k₀)).geometricFiber))).obj
          (0 : ProEtaleWeilSheaf k₀ l X)) :=
    Functor.isZero _ fun _ ↦ isZero_zero _
  have hadd : ((Functor.const _).obj (0 : ProEtaleWeilSheaf k₀ l X) :
      Mod (Sheaf (Scheme.ProEt.topology
        (X ↘ Spec (CommRingCat.of k₀)).geometricFiber) Ab.{u + 1})
        (condensedRingObj (Profinite.padicAlgClRingObj l)
          (X ↘ Spec (CommRingCat.of k₀)).geometricFiber) ⥤ _).Additive :=
    ⟨fun {_ _ _ _} ↦ (isZero_zero _).eq_of_src _ _⟩
  { E := (Functor.const _).obj 0
    R := condensedRealization k₀ l X
    e_add := hadd
    e_lim := ⟨fun J _ _ ↦ Functor.preservesLimitsOfShape_of_isZero _ hE J⟩
    e_colim := ⟨fun J _ _ ↦ Functor.preservesColimitsOfShape_of_isZero _ hE J⟩
    e_zero := Functor.preservesZeroMorphisms_of_additive _
    SA := Functor.uncurry.obj (curriedTensor _)
    SB := nativeOpenSheafTensor k₀ l X
    TA := (curriedTensor _).map₂CochainComplex
    TB := nativeTensorTotal k₀ l X
    DA := Functor.uncurry.obj (curriedTensor _)
    DB := nativeDerivedTensor k₀ l X
    flatA := CondensedIsKFlat k₀ l X
    flatB := NativeIsKFlat k₀ l X }

attribute [local instance] OpenTensorDescentInput.e_add OpenTensorDescentInput.r_add
  OpenTensorDescentInput.e_lim OpenTensorDescentInput.e_colim
  OpenTensorDescentInput.r_lim OpenTensorDescentInput.r_colim
  OpenTensorDescentInput.e_zero OpenTensorDescentInput.r_zero in
/-- The representative models and sheaf maps for the condensed realization descent: the native
and condensed K-flat models, the actual summand insertions, and the sheaf-level comparison
`condensedRealizationSheafTensorIso`. The extension comparison is between zero objects. -/
def condensedRealizationTensorModels :
    OpenTensorDescentModels (condensedRealizationTensorInput k₀ l X) where
  modelA := condensedTensorModel k₀ l X
  modelB := nativeOpenTensorModel k₀ l X
  iA P T p q n h := HomologicalComplex.ιMapBifunctor P T (curriedTensor _) (.up ℤ) p q n h
  iB := nativeOpenTensorInsertion k₀ l X
  sheafGamma _ N :=
    have := (tensorIhomAdjunction k₀ l X N).left_adjoint_additive
    IsZero.iso ((tensorFunctor k₀ l X N).map_isZero (isZero_zero _)) (isZero_zero _)
  sheafRestriction M N := (condensedRealizationSheafTensorIso k₀ l X).app (M, N)

end AlgebraicGeometry.ProEtaleWeilSheaf
