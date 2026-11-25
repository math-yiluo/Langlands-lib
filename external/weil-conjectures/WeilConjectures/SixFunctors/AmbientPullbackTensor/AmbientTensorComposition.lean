/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.AmbientPullbackTensor.AmbientPullbackTensorData
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainInverseComparison
import all Mathlib.Algebra.Category.Ring.Limits
import all WeilConjectures.CategoryTheory.RingedSiteModules
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import all WeilConjectures.CategoryTheory.AlgebraicInverseImage
import all Mathlib.Algebra.Category.ModuleCat.Sheaf
import all Mathlib.Algebra.Category.Grp.Limits
import all Mathlib.CategoryTheory.Sites.Whiskering
import all Mathlib.CategoryTheory.Sites.Equivalence
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
import all WeilConjectures.Algebra.Homology.Site.SiteTensorFunctorialitySupplement
import all WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import all WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import all Mathlib.Algebra.Category.Grp.FilteredColimits
import all Mathlib.Algebra.Homology.BifunctorShift
import all Mathlib.Algebra.Homology.QuasiIso
import all Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import all Mathlib.CategoryTheory.Limits.EssentiallySmall
import all WeilConjectures.Mathlib.Algebra.Homology.Monoidal
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import all Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import all Mathlib.CategoryTheory.Adjunction.Limits
import all WeilConjectures.CategoryTheory.AdjunctionRingOperations
import all Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
import all Mathlib.CategoryTheory.Adjunction.Basic
import all WeilConjectures.CategoryTheory.GeometricModuleConstruction
import all WeilConjectures.CategoryTheory.RingedToposRingData
import all WeilConjectures.CategoryTheory.Ringed.RingedToposMorphismSupplement
import all Mathlib.CategoryTheory.Sites.CartesianMonoidal
import all Mathlib.CategoryTheory.Monoidal.CommGrp_
import all WeilConjectures.Mathlib.CategoryTheory.Monoidal.Mod
import all WeilConjectures.CategoryTheory.GeometricModuleTransport
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
import WeilConjectures.AlgebraicGeometry.Tensor.TensorComparisonComposition

/-! # Components of ambient pullback coherence

Source: Stacks 03CB, 03D3, 03EL, 07A4 and 04VG.
(blueprint: lem-sf-ambient-normalized-tensor-composition).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
universe t u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open WeilConjectures.SemilinearSections
namespace WeilConjectures.AmbientPullbackTensor
variable (ell : ℕ) [Fact ell.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[ell] E] [FiniteDimensional ℚ_[ell] E]
attribute [local irreducible] pull CategoryTheory.Functor.leftAdjoint
  CategoryTheory.Functor.mapDerivedCategory

private theorem pure_eq (X : Scheme.{t}) (s : Option ℕ)
    (M N : Modules ell E X s) (U : (Site X s)ᵒᵖ)
    (x : M.val.obj U) (y : N.val.obj U) :
    SheafOfModules.CochainScalarConstruction.pure (coefficients ell E X s) M N U x y =
      pure ell E X s M N U x y := by
  unfold SheafOfModules.CochainScalarConstruction.pure pure tensorSectionAtSize
  rfl

private theorem generator_one_id {X Y : Scheme.{t}} (f : X ⟶ Y) (s : Option ℕ)
    (M : Modules ell E Y s) (U : Site Y s) (m : M.val.obj (op U)) :
    generator ell E f s M U ((base f s).obj U) (𝟙 _) m 1 =
      ((adjunction ell E f s).unit.app M).val.app (op U) m := by
  simp only [generator, op_id, PresheafOfModules.map_id]
  exact one_smul
    ((ring (topology X s) (coefficients ell E X s)).obj.obj (op ((base f s).obj U)))
    (show ((pull ell E f s).obj M).val.obj (op ((base f s).obj U)) from
      ((adjunction ell E f s).unit.app M).val.app (op U) m)

private theorem generator_map {X Y : Scheme.{t}} (f : X ⟶ Y) (s : Option ℕ)
    {M N : Modules ell E Y s} (a : M ⟶ N) (U : Site Y s) (V : Site X s)
    (q : V ⟶ (base f s).obj U) (m : M.val.obj (op U))
    (r : (coefficients ell E X s).obj.obj (op V)) :
    ((pull ell E f s).map a).val.app (op V) (generator ell E f s M U V q m r) =
      generator ell E f s N U V q (a.val.app (op U) m) r := by
  change (ring (topology X s) (coefficients ell E X s)).obj.obj (op V) at r
  refine ((((pull ell E f s).map a).val.app (op V)).hom.map_smul r
    (show ((pull ell E f s).obj M).val.obj (op V) from
      ((pull ell E f s).obj M).val.map q.op
        (((adjunction ell E f s).unit.app M).val.app (op U) m))).trans ?_
  apply congrArg (fun z : ((pull ell E f s).obj N).val.obj (op V) ↦ r • z)
  have hn := congrArg (fun z ↦ z.val.app (op U) m)
    ((adjunction ell E f s).unit.naturality a)
  have hq := PresheafOfModules.naturality_apply ((pull ell E f s).map a).val q.op
    (((adjunction ell E f s).unit.app M).val.app (op U) m)
  exact hq.trans (congrArg (fun z ↦ ((pull ell E f s).obj N).val.map q.op z) hn.symm)

private theorem ordinary_composition {X Y Z : Scheme.{t}}
    (f : X ⟶ Y) (g : Y ⟶ Z) (s : Option ℕ)
    (A : Tensor ell E Z s) (B : Tensor ell E Y s) (C : Tensor ell E X s)
    (TA : TensorModels ell E Z s A) (TB : TensorModels ell E Y s B)
    (TC : TensorModels ell E X s C)
    (Kf : TensorData ell E f s B C TB TC) (Kg : TensorData ell E g s A B TA TB)
    (Kh : TensorData ell E (f ≫ g) s A C TA TC)
    (_hKf : Kf.Normalized ell E f s B C TB TC)
    (_hKg : Kg.Normalized ell E g s A B TA TB)
    (_hKh : Kh.Normalized ell E (f ≫ g) s A C TA TC)
    (_hgen : (∀ (M : Modules ell E Z s) (U : Site Z s) (V : Site Y s) (W : Site X s)
      (p : V ⟶ (base g s).obj U) (q : W ⟶ (base f s).obj V)
      (m : M.val.obj (op U)) (a : (coefficients ell E Y s).obj.obj (op V))
      (b : (coefficients ell E X s).obj.obj (op W)),
      ((comp ell E f g s).hom.app M).val.app (op W)
          (generator ell E f s ((pull ell E g s).obj M) V W q
            (generator ell E g s M U V p m a) b) =
        generator ell E (f ≫ g) s M U W
          (q ≫ (base f s).map p ≫ (baseComp f g s).inv.app U) m
          (scalar ell E f s V W q a * b))) :
    (∀ (M N : Modules ell E Z s),
      (pull ell E f s).map (Kg.model.ordinary M N).hom ≫
          (Kf.model.ordinary
            ((pull ell E g s).obj M) ((pull ell E g s).obj N)).hom ≫
          tensorHom ell E X s ((comp ell E f g s).hom.app M)
            ((comp ell E f g s).hom.app N) =
        (comp ell E f g s).hom.app (tensor ell E Z s M N) ≫
          (Kh.model.ordinary M N).hom) := by
  have generator_map {X Y : Scheme.{t}} (f : X ⟶ Y) (s : Option ℕ)
      {M N : Modules ell E Y s} (a : M ⟶ N) (U : Site Y s) (V : Site X s)
      (q : V ⟶ (base f s).obj U) (m : M.val.obj (op U))
      (r : (coefficients ell E X s).obj.obj (op V)) :
      ((pull ell E f s).map a).val.app (op V) (generator ell E f s M U V q m r) =
        generator ell E f s N U V q (a.val.app (op U) m) r := by
    change (ring (topology X s) (coefficients ell E X s)).obj.obj (op V) at r
    refine ((((pull ell E f s).map a).val.app (op V)).hom.map_smul r
      (show ((pull ell E f s).obj M).val.obj (op V) from
        ((pull ell E f s).obj M).val.map q.op
          (((adjunction ell E f s).unit.app M).val.app (op U) m))).trans ?_
    apply congrArg (fun z : ((pull ell E f s).obj N).val.obj (op V) ↦ r • z)
    have hn := congrArg (fun z ↦ z.val.app (op U) m)
      ((adjunction ell E f s).unit.naturality a)
    have hq := PresheafOfModules.naturality_apply ((pull ell E f s).map a).val q.op
      (((adjunction ell E f s).unit.app M).val.app (op U) m)
    exact hq.trans (congrArg (fun z ↦ ((pull ell E f s).obj N).val.map q.op z) hn.symm)
  intro M N
  apply (((adjunction ell E g s).comp (adjunction ell E f s)).homEquiv _ _).injective
  apply SheafOfModules.CochainScalarConstruction.pure_hom_ext
    (coefficients ell E Z s) M N _
  intro U x y
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
  let V := (base g s).obj U.unop
  let W := (base f s).obj V
  suffices hs : (tensorHom ell E X s ((comp ell E f g s).hom.app M)
      ((comp ell E f g s).hom.app N)).val.app (op W)
      ((Kf.model.ordinary _ _).hom.val.app (op W)
        (((pull ell E f s).map (Kg.model.ordinary M N).hom).val.app (op W)
          (generator ell E f s ((pull ell E g s).obj (tensor ell E Z s M N))
            V W (𝟙 _) (generator ell E g s (tensor ell E Z s M N)
              U.unop V (𝟙 _) (pure ell E Z s M N U x y) 1) 1))) =
    (Kh.model.ordinary M N).hom.val.app (op W)
      (((comp ell E f g s).hom.app (tensor ell E Z s M N)).val.app (op W)
        (generator ell E f s ((pull ell E g s).obj (tensor ell E Z s M N))
          V W (𝟙 _) (generator ell E g s (tensor ell E Z s M N)
            U.unop V (𝟙 _) (pure ell E Z s M N U x y) 1) 1)) by
    simp only [V, W, generator_one_id] at hs
    simp only [Adjunction.comp_unit_app, pure_eq]
    dsimp only [push, moduleRingUnit, SheafOfModules.pushforward,
      PresheafOfModules.pushforward, PresheafOfModules.pushforward₀,
      PresheafOfModules.pushforward₀Obj, PresheafOfModules.restrictScalars,
      ModuleCat.restrictScalars]
    exact hs
  rw [generator_map, _hKg.1, _hKf.1]
  have ht := SheafOfModules.CochainScalarConstruction.pure_map (coefficients ell E X s)
    ((comp ell E f g s).hom.app M) ((comp ell E f g s).hom.app N) (op W)
    (generator ell E f s ((pull ell E g s).obj M) V W (𝟙 _)
      (generator ell E g s M U.unop V (𝟙 _) x 1) 1)
    (generator ell E f s ((pull ell E g s).obj N) V W (𝟙 _)
      (generator ell E g s N U.unop V (𝟙 _) y 1) 1)
  simp only [pure_eq] at ht
  erw [ht]
  rw [_hgen, _hgen, _hgen, _hKh.1]
  simp only [scalar, map_one, one_mul]

/-- Ordinary tensor composition and its total and derived representative equations.
Source: Stacks 03EL, 06YN, 07A4, 0G7E and 0G7D
(blueprint: lem-sf-ambient-normalized-tensor-composition).
Proof: transpose the ordinary equality under the composite module adjunction and
test on sheafified pure tensors. The three normalization equations and hgen send
both routes to the tensor of the two composite generators, with the product of
intermediate scalars in the first factor and 1 in the second. Tensor balancing
and the sheafification universal property extend equality to module morphisms.
For complexes, invert the ordinary equality and use the model.summand equations.
The total tensor functor maps the two chain comparators degreewise. Its summand
inclusions reduce the displayed chain equality to that inverse ordinary equation;
naturality handles both signed differentials. Direct-sum universality proves the
chain equality. Resolve both inputs on the whole ringed site by flat-term K-flat
complexes. The normalization hypotheses preserve that representative class under
successive pullback. Substitute the model.derived equations and the exact
factorization of derivedComp into the localization of the chain equality, and
cancel the invertible representative comparisons. Cochain tensor rigidity, or
the resolving-subcategory localization universal property, extends the resulting
natural-transformation equality to all unbounded inputs. These steps are on the
sequence site itself and use no cartesian-system or flat-transition hypothesis. -/
theorem normalizedTensor_composition {X Y Z : Scheme.{t}}
    (f : X ⟶ Y) (g : Y ⟶ Z) (s : Option ℕ)
    (A : Tensor ell E Z s) (B : Tensor ell E Y s) (C : Tensor ell E X s)
    (TA : TensorModels ell E Z s A) (TB : TensorModels ell E Y s B)
    (TC : TensorModels ell E X s C)
    (Kf : TensorData ell E f s B C TB TC) (Kg : TensorData ell E g s A B TA TB)
    (Kh : TensorData ell E (f ≫ g) s A C TA TC)
    (_hKf : Kf.Normalized ell E f s B C TB TC)
    (_hKg : Kg.Normalized ell E g s A B TA TB)
    (_hKh : Kh.Normalized ell E (f ≫ g) s A C TA TC)
    (_hgen : (∀ (M : Modules ell E Z s) (U : Site Z s) (V : Site Y s) (W : Site X s)
      (p : V ⟶ (base g s).obj U) (q : W ⟶ (base f s).obj V)
      (m : M.val.obj (op U)) (a : (coefficients ell E Y s).obj.obj (op V))
      (b : (coefficients ell E X s).obj.obj (op W)),
      ((comp ell E f g s).hom.app M).val.app (op W)
          (generator ell E f s ((pull ell E g s).obj M) V W q
            (generator ell E g s M U V p m a) b) =
        generator ell E (f ≫ g) s M U W
          (q ≫ (base f s).map p ≫ (baseComp f g s).inv.app U) m
          (scalar ell E f s V W q a * b))) :
    (∀ (M N : Modules ell E Z s),
      (pull ell E f s).map (Kg.model.ordinary M N).hom ≫
          (Kf.model.ordinary
            ((pull ell E g s).obj M) ((pull ell E g s).obj N)).hom ≫
          tensorHom ell E X s ((comp ell E f g s).hom.app M)
            ((comp ell E f g s).hom.app N) =
        (comp ell E f g s).hom.app (tensor ell E Z s M N) ≫
          (Kh.model.ordinary M N).hom) ∧
    (∀ P Q : CochainComplex (Modules ell E Z s) ℤ,
      FlatRepresentative ell E Z s P → FlatRepresentative ell E Z s Q →
      (total ell E X s).map (Prod.mkHom (chainComp ell E f g s P)
          (chainComp ell E f g s Q)) ≫
          Kh.model.chain P Q =
        Kf.model.chain
            (((pull ell E g s).mapHomologicalComplex (.up ℤ)).obj P)
            (((pull ell E g s).mapHomologicalComplex (.up ℤ)).obj Q) ≫
          ((pull ell E f s).mapHomologicalComplex (.up ℤ)).map
            (Kg.model.chain P Q) ≫
          chainComp ell E f g s ((total ell E Z s).obj (P, Q))) ∧
    ∀ F G : Derived ell E Z s,
      (derivedPull ell E f s).map (Kg.mu.hom.app (F, G)) ≫
          Kf.mu.hom.app
            ((derivedPull ell E g s).obj F, (derivedPull ell E g s).obj G) ≫
          C.tensor.map (Prod.mkHom ((derivedComp ell E f g s).hom.app F)
            ((derivedComp ell E f g s).hom.app G)) =
        (derivedComp ell E f g s).hom.app (A.tensor.obj (F, G)) ≫
          Kh.mu.hom.app (F, G) := by
  have ho := ordinary_composition ell E f g s A B C TA TB TC Kf Kg Kh
    _hKf _hKg _hKh _hgen
  obtain ⟨hc, hd⟩ := tensorComparisonComposition.{t + 1, t, u}
    (topology Z s) (topology Y s) (topology X s)
    (coefficients ell E Z s) (coefficients ell E Y s) (coefficients ell E X s)
    (pull ell E g s) (pull ell E f s) (pull ell E (f ≫ g) s)
    A B C TA TB TC Kg Kf Kh (comp ell E f g s) ho
  refine ⟨ho, ?_, hd⟩
  intro P Q _ _
  simpa only [chainComp] using hc P Q

end WeilConjectures.AmbientPullbackTensor
