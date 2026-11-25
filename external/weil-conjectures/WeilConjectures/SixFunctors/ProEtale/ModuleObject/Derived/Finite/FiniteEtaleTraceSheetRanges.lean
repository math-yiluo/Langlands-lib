/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Finite.FiniteEtaleLatticeSheetMaps
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Finite.FiniteEtaleTraceFormula
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Continuous.ContinuousLatticeSumFree
public import WeilConjectures.AlgebraicGeometry.Continuous.ContinuousLatticeSum
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
import WeilConjectures.AlgebraicGeometry.ComapUpperStarIsoMate
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ProperBaseChange.ComapUpperStarIsoComposition
import WeilConjectures.AlgebraicGeometry.SplitProEtaleModuleProductMap
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs
import Mathlib.CategoryTheory.Limits.Shapes.Products
import WeilConjectures.AlgebraicGeometry.ProfinitePointPullback
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import WeilConjectures.AlgebraicGeometry.ProEtaleInverseImage
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs
import WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
import Mathlib.AlgebraicGeometry.Sites.Proetale
import Mathlib.CategoryTheory.Sites.ConstantSheaf
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import WeilConjectures.CategoryTheory.RingedSiteModules
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous
import Mathlib.CategoryTheory.Sites.Equivalence
import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.Defs
import WeilConjectures.Mathlib.CategoryTheory.Sites.Monoidal
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Category.ModuleCat.AB
import Mathlib.Algebra.Category.ModuleCat.Sheaf
import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import Mathlib.CategoryTheory.Sites.Sheafification
import WeilConjectures.CategoryTheory.Adjunction.LiftsGroupRingObjects
import Mathlib.CategoryTheory.Monoidal.CommGrp_
import Mathlib.CategoryTheory.Monoidal.Ring
import Mathlib.CategoryTheory.Adjunction.Limits
import WeilConjectures.CategoryTheory.Adjunction.LiftedCommRingBranch
import WeilConjectures.CategoryTheory.Monoidal.Conjugate
import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate
import WeilConjectures.CategoryTheory.Sites.MonObj
import WeilConjectures.AlgebraicGeometry.SplitProEtaleAbelianProductMap
import Mathlib.Algebra.Category.Grp.AB
import WeilConjectures.Mathlib.CategoryTheory.Adjunction.Unique
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Defs
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Iso
import WeilConjectures.Mathlib.AlgebraicGeometry.PullbackCarrier
import Mathlib.AlgebraicGeometry.Limits
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Submodule
import Mathlib.Algebra.Category.Grp.Ulift

/-! # Section ranges of a trace image on a specified splitting

Source: blueprint, stratified lattice trace proof, Local computation, paragraph 1.
(blueprint: lem-sfb-finite-etale-trace-sheet-ranges)
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u v
open CategoryTheory Limits Opposite
open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.CondensedRing

private theorem map_image_factorization
    {C D : Type*} [Category C] [Category D] (F : C ⥤ D)
    {X Y : C} (f : X ⟶ Y) [HasImage f] {Z : D} (a : F.obj Y ⟶ Z) :
    F.map (factorThruImage f) ≫ (F.map (image.ι f) ≫ a) = F.map f ≫ a := by
  rw [← F.map_comp_assoc, image.fac]

private theorem image_range_of_sheaf_submodule
    {C : Type*} [Category C] {J : GrothendieckTopology C}
    {R : Sheaf J RingCat.{u}} [HasSheafify J Ab.{v}] [J.WEqualsLocallyBijective Ab.{v}]
    {A B I : SheafOfModules.{v} R} (f : A ⟶ B) (e : A ⟶ I) (i : I ⟶ B)
    [Epi e] (h : e ≫ i = f) (D : B.val.Submodule)
    (hD : Presheaf.IsSheaf J D.toPresheafOfModules.presheaf)
    (hf : ∀ T, Set.range (f.val.app T) = (D.obj T : Set (B.val.obj T))) :
    ∀ T, Set.range (i.val.app T) = (D.obj T : Set (B.val.obj T)) := by
  let N : SheafOfModules R := ⟨D.toPresheafOfModules, hD⟩
  let j : N ⟶ B := ⟨D.ι⟩
  have : Mono j := (SheafOfModules.forget R).mono_of_mono_map
    (show Mono D.ι from inferInstance)
  let f' : A ⟶ N :=
    ⟨{ app := fun T ↦ ModuleCat.ofHom
        ((f.val.app T).hom.codRestrict (D.obj T) (fun x ↦ (hf T).le ⟨x, rfl⟩))
       naturality := by
         intro T U a
         ext x
         exact Subtype.ext (PresheafOfModules.naturality_apply f.val a x) }⟩
  have hfj : f' ≫ j = f := by ext T x; rfl
  have hi : i ≫ cokernel.π j = 0 := by
    apply (cancel_epi e).mp
    rw [← Category.assoc, h, ← hfj, Category.assoc, cokernel.condition, comp_zero,
      comp_zero]
  let k := Abelian.monoLift j i hi
  have hk : k ≫ j = i := Abelian.monoLift_comp j i hi
  intro T
  apply Set.Subset.antisymm
  · rintro _ ⟨x, rfl⟩
    have hx := congrArg (fun z ↦ z.val.app T x) hk
    let y : D.obj T := k.val.app T x
    have hy : (y : B.val.obj T) = i.val.app T x := hx
    exact hy ▸ y.property
  · intro x hx
    obtain ⟨y, rfl⟩ := (hf T).ge hx
    refine ⟨e.val.app T y, ?_⟩
    exact congrArg (fun z ↦ z.val.app T y) h

private theorem sum_section_ranges
    {C : Type*} [Category C] [Preadditive C]
    {J : Type} [Fintype J] (M : J → C) [HasProduct M]
    {S Q : C} (q : ∀ j, S ⟶ M j) (hq : IsIso (Pi.lift q)) (s : ∀ j, M j ⟶ Q)
    {A : Type*} [Ring A] (H : C ⥤ ModuleCat.{v} A) [H.Additive]
    {V : Type*} [AddCommGroup V] {B : Type*} [Ring B] [Module B V]
    (c : H.obj Q ≃+ V) (N : J → Submodule B V)
    (hs : ∀ j, Set.range (fun x ↦ c (H.map (s j) x)) = (N j : Set V)) :
    Set.range (fun x ↦ c (H.map (∑ j, q j ≫ s j) x)) = (⨆ j, N j : Submodule B V) := by
  classical
  let : IsIso (Pi.lift q) := hq
  let : HasBiproduct M := HasBiproduct.of_hasProduct M
  let b : S ⟶ ⨁ M := biproduct.lift q
  have hb : b ≫ (biproduct.isoProduct M).hom = Pi.lift q := by
    apply Pi.hom_ext
    intro j
    simp [b, biproduct.isoProduct_hom]
  have : IsIso b := by
    have : IsIso (b ≫ (biproduct.isoProduct M).hom) := hb ▸ inferInstance
    exact IsIso.of_isIso_comp_right b (biproduct.isoProduct M).hom
  let f : S ⟶ Q := ∑ j, q j ≫ s j
  have hf : b ≫ biproduct.desc s = f :=
    biproduct.lift_desc (g := q) (h := s)
  let a (j : J) : M j ⟶ S := biproduct.ι M j ≫ inv b
  have ha (j : J) : a j ≫ f = s j := by
    rw [← hf]
    simp [a, Category.assoc]
  have happ (x : H.obj S) :
      c (H.map f x) = ∑ j, c (H.map (s j) (H.map (q j) x)) := by
    dsimp only [f]
    rw [H.map_sum]
    change c ((∑ j, H.map (q j ≫ s j)).hom x) = _
    rw [ModuleCat.hom_sum, LinearMap.sum_apply, map_sum]
    simp only [H.map_comp, ModuleCat.hom_comp, LinearMap.comp_apply]
  apply Set.Subset.antisymm
  · rintro _ ⟨x, rfl⟩
    change c (H.map f x) ∈ (⨆ j, N j)
    rw [happ]
    exact Submodule.sum_mem _ fun j _ ↦ le_iSup N j ((hs j).le ⟨_, rfl⟩)
  · intro x hx
    have hx' : x ∈ ⨆ j ∈ (Finset.univ : Finset J), N j := by simpa using hx
    obtain ⟨y, hy⟩ := (Submodule.mem_iSup_finset_iff_exists_sum N x).mp hx'
    have hy' : ∑ j, (y j : V) = x := by simpa using hy
    choose z hz using fun j ↦ (hs j).ge (y j).property
    refine ⟨∑ j, H.map (a j) (z j), ?_⟩
    change c (H.map f (∑ j, H.map (a j) (z j))) = x
    rw [map_sum, map_sum]
    convert hy' using 1
    apply Finset.sum_congr rfl
    intro j _
    rw [← ConcreteCategory.comp_apply, ← H.map_comp, ha]
    exact hz j

private theorem encoded_sum_section_ranges
    {C : Type*} [Category C] [Preadditive C]
    {D : Type*} [Category D] {J : GrothendieckTopology D}
    {R : Sheaf J RingCat.{u}} (F : C ⥤ SheafOfModules.{v} R) [F.Additive]
    {I : Type} [Fintype I] (M : I → C) [HasProduct M]
    {S Q : C} (q : ∀ j, S ⟶ M j) (hq : IsIso (Pi.lift q)) (s : ∀ j, M j ⟶ Q)
    (T : Dᵒᵖ) {V : Type*} [AddCommGroup V] {A : Type*} [Ring A] [Module A V]
    (c : (F.obj Q).val.obj T ≃+ V) (N : I → Submodule A V)
    (hs : ∀ j, Set.range (fun x ↦ c ((F.map (s j)).val.app T x)) = (N j : Set V)) :
    Set.range (fun x ↦ c ((F.map (∑ j, q j ≫ s j)).val.app T x)) =
      (⨆ j, N j : Submodule A V) := by
  let H := F ⋙ SheafOfModules.evaluation R T
  let : (SheafOfModules.evaluation R T).Additive := by
    dsimp [SheafOfModules.evaluation]
    infer_instance
  let : H.Additive := by dsimp only [H]; infer_instance
  exact sum_section_ranges M q hq s H c N hs

section Coordinates
variable {E : Type} [NormedField E] (A : Subring E) [TotallyDisconnectedSpace A]
  {X : Scheme.{u}} {r : ℕ}
  (Q : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
    (condensedRingObj (Profinite.continuousMapRingObj A) X))
  (c : ContinuousFunctionPresentation X A (Fin r → E) Q)
  (N : Submodule A (Fin r → E))

private def coordinateSubmodule :
    ((continuousRingModuleEquivalence X A).functor.obj Q).val.Submodule where
  obj B :=
    { carrier := {x | ∀ z, c.sections B.unop x z ∈ N}
      zero_mem' := by intro z; simp
      add_mem' := by
        intro x y hx hy z
        simpa only [map_add, ContinuousMap.add_apply] using N.add_mem (hx z) (hy z)
      smul_mem' := by
        intro a x hx z
        rw [c.smul]
        exact N.smul_mem (a.down z) (hx z) }
  map {B D} a := by
    intro x hx z
    change c.sections D.unop
      (((continuousRingModuleEquivalence X A).functor.obj Q).val.map a x) z ∈ N
    have h := congrArg (fun f ↦ f z) (c.restrict B.unop D.unop a.unop x)
    exact h.symm ▸ hx (a.unop.left.base z)

private theorem coordinateSubmodule_mem_iff
    (B : X.ProEt)
    (x : ((continuousRingModuleEquivalence X A).functor.obj Q).val.obj (op B)) :
    x ∈ (coordinateSubmodule A Q c N).obj (op B) ↔
      c.sections B x ∈ Set.range (continuousLatticeInclusion A N B.left) := by
  constructor
  · intro hx
    exact ⟨⟨fun z ↦ ⟨c.sections B x z, hx z⟩,
      (c.sections B x).continuous.subtype_mk _⟩, rfl⟩
  · rintro ⟨y, hy⟩ z
    exact (congrArg (fun f ↦ f z) hy) ▸ (y z).property

private theorem coordinateSubmodule_isSheaf :
    Presheaf.IsSheaf (Scheme.ProEt.topology X)
      (coordinateSubmodule A Q c N).toPresheafOfModules.presheaf := by
  let D := coordinateSubmodule A Q c N
  let F := (Scheme.ProEt.forget X ⋙ Over.forget X).op ⋙ continuousMapPresheafAb N
  let e (B : X.ProEtᵒᵖ) : D.obj B ≃+ ULift.{u + 1} C(B.unop.left, N) :=
    { toFun := fun x ↦ ULift.up
        ⟨fun z ↦ ⟨c.sections B.unop x.val z, x.property z⟩,
          (c.sections B.unop x.val).continuous.subtype_mk _⟩
      invFun := fun y ↦ ⟨(c.sections B.unop).symm
        (continuousLatticeInclusion A N B.unop.left y.down), by
          intro z
          simp only [AddEquiv.apply_symm_apply]
          exact (y.down z).property⟩
      left_inv := by
        intro x
        apply Subtype.ext
        apply (c.sections B.unop).injective
        simp only [AddEquiv.apply_symm_apply]
        rfl
      right_inv := by
        intro y
        apply ULift.ext
        ext z
        simp only [AddEquiv.apply_symm_apply]
        rfl
      map_add' := by
        intro x y
        apply ULift.ext
        ext z
        simp }
  let α : D.toPresheafOfModules.presheaf ≅ F ⋙ AddCommGrpCat.uliftFunctor.{u + 1} :=
    NatIso.ofComponents (fun B ↦ (e B).toAddCommGrpIso) (by
      intro B B' a
      ext x
      apply ULift.ext
      change (e B' (D.toPresheafOfModules.map a x)).down =
        (e B x).down.comp a.unop.left.base.hom
      apply ContinuousMap.ext
      intro z
      apply Subtype.ext
      exact congrArg (fun f ↦ f z) (c.restrict B.unop B'.unop a.unop x.val))
  apply (Presheaf.isSheaf_of_iso_iff α).mpr
  apply Presheaf.isSheaf_comp_of_isSheaf
  apply Functor.op_comp_isSheaf_of_isSheaf _ _ Scheme.proetaleTopology
  exact Presheaf.IsSheaf.of_le Scheme.proetaleTopology_le_fpqcTopology
    (isSheaf_fpqcTopology_continuousMapPresheafAb N)

end Coordinates

private theorem presented_sum_ranges
    {E : Type} [NormedField E] (A : Subring E) [TotallyDisconnectedSpace A]
    {Y : Scheme.{u}} {r d : ℕ}
    (Z Q : Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousMapRingObj A) Y))
    (M : Fin d → Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousMapRingObj A) Y))
    (q : ∀ j, Z ⟶ M j) (hq : IsIso (Pi.lift q)) (s : ∀ j, M j ⟶ Q)
    (v : Z ⟶ Q) (hv : v = ∑ j, q j ≫ s j)
    (c : ContinuousFunctionPresentation Y A (Fin r → E) Q)
    (L : Fin d → Submodule A (Fin r → E))
    (hc : ∀ (j : Fin d) (B : Y.ProEt),
      Set.range (fun x ↦ c.sections B
        (((continuousRingModuleEquivalence Y A).functor.map (s j)).val.app (op B) x)) =
          Set.range (continuousLatticeInclusion A (L j) B.left)) :
    ∀ B : Y.ProEt,
      Set.range (fun x ↦ c.sections B
        (((continuousRingModuleEquivalence Y A).functor.map v).val.app (op B) x)) =
          ↑(⨆ j, (continuousLatticeInclusion A (L j) B.left).range) := by
  let F := (continuousRingModuleEquivalence Y A).functor
  let : F.Additive := Functor.additive_of_preserves_binary_products F
  intro B
  rw [hv]
  exact encoded_sum_section_ranges (R := continuousMapRingSheaf Y A)
    (S := Z) (Q := Q) (V := C(B.left, Fin r → E)) (A := C(B.left, A))
    F M q hq s (op B) (c.sections B)
    (fun j ↦ (continuousLatticeInclusion A (L j) B.left).range) (hc · B)

private theorem presented_image_ranges
    {E : Type} [NormedField E] (A : Subring E) [TotallyDisconnectedSpace A]
    {Y : Scheme.{u}} {r d : ℕ}
    (Z I Q : Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousMapRingObj A) Y))
    (v : Z ⟶ Q) (e : Z ⟶ I) [Epi e] (i : I ⟶ Q) (hei : e ≫ i = v)
    (c : ContinuousFunctionPresentation Y A (Fin r → E) Q)
    (L : Fin d → Submodule A (Fin r → E))
    (hcoor : ∀ B : Y.ProEt,
      Set.range (fun x ↦ c.sections B
        (((continuousRingModuleEquivalence Y A).functor.map v).val.app (op B) x)) =
          ↑(⨆ j, (continuousLatticeInclusion A (L j) B.left).range))
    (hsum : ∀ B : Y.ProEt,
      (⨆ j, (continuousLatticeInclusion A (L j) B.left).range) =
        (continuousLatticeInclusion A (⨆ j, L j) B.left).range) :
    ∀ B : Y.ProEt,
      Set.range (fun x ↦ c.sections B
        (((continuousRingModuleEquivalence Y A).functor.map i).val.app (op B) x)) =
          ↑(⨆ j, (continuousLatticeInclusion A (L j) B.left).range) := by
  let F := (continuousRingModuleEquivalence Y A).functor
  let f := F.map v
  let i' := F.map i
  let e' := F.map e
  have hei' : e' ≫ i' = f := by
    change F.map e ≫ F.map i = F.map v
    rw [← F.map_comp, hei]
  have hsumset (B : Y.ProEt) :
      (↑(⨆ j, (continuousLatticeInclusion A (L j) B.left).range) :
        Set C(B.left, Fin r → E)) =
          Set.range (continuousLatticeInclusion A (⨆ j, L j) B.left) := by
    simpa only [LinearMap.coe_range] using
      congrArg (fun N : Submodule C(B.left, A) C(B.left, Fin r → E) ↦
        (N : Set C(B.left, Fin r → E)))
        (hsum B)
  let D := coordinateSubmodule A Q c (⨆ j, L j)
  have hf : ∀ T, Set.range (f.val.app T) = (D.obj T : Set _) := by
    intro T
    ext x
    constructor
    · rintro ⟨y, rfl⟩
      apply (coordinateSubmodule_mem_iff A Q c (⨆ j, L j) T.unop _).mpr
      exact (hsumset T.unop).le ((hcoor T.unop).le ⟨y, rfl⟩)
    · intro hx
      have hx' := (coordinateSubmodule_mem_iff A Q c (⨆ j, L j) T.unop x).mp hx
      obtain ⟨y, hy⟩ := (hcoor T.unop).ge ((hsumset T.unop).ge hx')
      exact ⟨y, (c.sections T.unop).injective hy⟩
  have hImage := image_range_of_sheaf_submodule f e' i' hei' D
    (coordinateSubmodule_isSheaf A Q c (⨆ j, L j)) hf
  intro B
  have hif := (hImage (op B)).trans (hf (op B)).symm
  have hcoords : Set.range (fun x ↦ c.sections B (i'.val.app (op B) x)) =
      Set.range (fun x ↦ c.sections B (f.val.app (op B) x)) := by
    simpa only [Set.range_comp'] using congrArg (Set.image (c.sections B)) hif
  exact hcoords.trans (hcoor B)

private theorem lattice_sum_section_ranges
    (l : ℕ) [Fact l.Prime] (E : Type) [NormedField E]
    [NormedAlgebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    [TotallyDisconnectedSpace E] (Y : Scheme.{u}) (r d : ℕ) [Nonempty (Fin d)] :
    ∀ (L : Fin d → Submodule (continuousIntegers l E) (Fin r → E)),
      (∀ j, ∃ b : Module.Basis (Fin r) (continuousIntegers l E) (L j),
        ∃ c : Module.Basis (Fin r) E (Fin r → E), ∀ i, (b i : Fin r → E) = c i) →
      ∀ B : Y.ProEt,
        (⨆ j, (continuousLatticeInclusion (continuousIntegers l E) (L j) B.left).range) =
          (continuousLatticeInclusion (continuousIntegers l E) (⨆ j, L j) B.left).range := by
  rw [continuousIntegers_eq l E]
  intro L hL B
  exact ((continuous_lattice_sum.{u, 0, 0, u} l E r (Fin d) L hL).2.2 Y).2.2.1 B

section TraceCompatibility

attribute [local irreducible] upperStar lowerStar upperStarComp upperStarLowerStarAdjunction
attribute [local irreducible] comapUpperStarIso comapLowerStarIso

private theorem sheet_counit_compatibility
    {R S : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
    [MonObj R] [IsCommMonObj R] [MonObj S] [IsCommMonObj S]
    (a : R ⟶ S) [IsMonHom a] {X U Y : Scheme.{u}}
    (p : U ⟶ X) (t : Y ⟶ U)
    (N : Mod (Sheaf (Scheme.ProEt.topology U) Ab.{u + 1}) (condensedRingObj S U)) :
    (upperStar R (t ≫ p)).map ((comapLowerStarIso a p).inv.app N) ≫
        (comapUpperStarIso a (t ≫ p)).inv.app ((lowerStar S p).obj N) ≫
        (Mod.comap (coefficientMap a Y)).map
          ((upperStarComp S t p).hom.app ((lowerStar S p).obj N) ≫
            (upperStar S t).map ((upperStarLowerStarAdjunction S p).counit.app N)) =
      (upperStarComp R t p).hom.app
          ((lowerStar R p).obj ((Mod.comap (coefficientMap a U)).obj N)) ≫
        (upperStar R t).map
          ((upperStarLowerStarAdjunction R p).counit.app
            ((Mod.comap (coefficientMap a U)).obj N)) ≫
        (comapUpperStarIso a t).inv.app N := by
  have hε := mateEquiv_counit (upperStarLowerStarAdjunction S p)
    (upperStarLowerStarAdjunction R p)
    (TwoSquare.mk _ _ _ _ (comapUpperStarIso a p).inv) N
  rw [comapUpperStarIso_mate] at hε
  replace hε := hε.symm
  change (comapUpperStarIso a p).inv.app ((lowerStar S p).obj N) ≫
      (Mod.comap (coefficientMap a U)).map
        ((upperStarLowerStarAdjunction S p).counit.app N) =
    (upperStar R p).map ((comapLowerStarIso a p).hom.app N) ≫
      (upperStarLowerStarAdjunction R p).counit.app
        ((Mod.comap (coefficientMap a U)).obj N) at hε
  have hcomp := comapUpperStarIso_comp (a := a) t p ((lowerStar S p).obj N)
  have hc :
      (comapUpperStarIso a (t ≫ p)).inv.app ((lowerStar S p).obj N) ≫
        (Mod.comap (coefficientMap a Y)).map
          ((upperStarComp S t p).hom.app ((lowerStar S p).obj N)) =
      (upperStarComp R t p).hom.app
          ((Mod.comap (coefficientMap a X)).obj ((lowerStar S p).obj N)) ≫
        (upperStar R t).map
          ((comapUpperStarIso a p).inv.app ((lowerStar S p).obj N)) ≫
        (comapUpperStarIso a t).inv.app
          ((upperStar S p).obj ((lowerStar S p).obj N)) := by
    rw [hcomp]
    simp only [Category.assoc]
    rw [← Functor.map_comp_assoc, Iso.hom_inv_id_app]
    erw [(upperStar R t).map_id,
      Category.id_comp, Iso.hom_inv_id_app, Category.comp_id]
  rw [Functor.map_comp, ← Category.assoc
    ((comapUpperStarIso a (t ≫ p)).inv.app _) _ _, hc]
  simp only [Category.assoc]
  erw [← Category.assoc, (upperStarComp R t p).hom.naturality
    ((comapLowerStarIso a p).inv.app N)]
  simp only [Functor.comp_map, Category.assoc]
  erw [← (comapUpperStarIso a t).inv.naturality
    ((upperStarLowerStarAdjunction S p).counit.app N)]
  simp only [Functor.comp_map]
  rw [← (upperStar R t).map_comp_assoc
    ((comapUpperStarIso a p).inv.app ((lowerStar S p).obj N))
    ((Mod.comap (coefficientMap a U)).map
      ((upperStarLowerStarAdjunction S p).counit.app N)), hε, Functor.map_comp]
  simp only [← Functor.map_comp_assoc, ← Functor.map_comp,
    Iso.inv_hom_id_app, (upperStar R p).map_id, Category.id_comp]
  rfl

private theorem sheet_embedding_compatibility
    {R S : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
    [MonObj R] [IsCommMonObj R] [MonObj S] [IsCommMonObj S]
    (a : R ⟶ S) [IsMonHom a] {X U Y : Scheme.{u}}
    (p : U ⟶ X) (g : Y ⟶ X) (t : Y ⟶ U) (w : t ≫ p = g)
    (M : Mod (Sheaf (Scheme.ProEt.topology U) Ab.{u + 1}) (condensedRingObj R U))
    (N : Mod (Sheaf (Scheme.ProEt.topology U) Ab.{u + 1}) (condensedRingObj S U))
    (h : M ⟶ (Mod.comap (coefficientMap a U)).obj N) :
    (upperStar R g).map ((lowerStar R p).map h ≫
        (comapLowerStarIso a p).inv.app N) ≫
        (comapUpperStarIso a g).inv.app ((lowerStar S p).obj N) ≫
        (Mod.comap (coefficientMap a Y)).map
          (((eqToIso (congrArg (upperStar S) w)).symm ≪≫
            upperStarComp S t p).hom.app ((lowerStar S p).obj N) ≫
            (upperStar S t).map ((upperStarLowerStarAdjunction S p).counit.app N)) =
      ((eqToIso (congrArg (upperStar R) w)).symm ≪≫
          upperStarComp R t p).hom.app ((lowerStar R p).obj M) ≫
        (upperStar R t).map ((upperStarLowerStarAdjunction R p).counit.app M) ≫
        (upperStar R t).map h ≫ (comapUpperStarIso a t).inv.app N := by
  subst g
  simp only [eqToIso_refl, Iso.refl_symm, Iso.refl_trans]
  rw [Functor.map_comp, Category.assoc, sheet_counit_compatibility]
  erw [← Category.assoc, (upperStarComp R t p).hom.naturality]
  simp only [Functor.comp_map, Category.assoc]
  rw [← Functor.map_comp_assoc]
  have hε := (upperStarLowerStarAdjunction R p).counit.naturality h
  change (upperStar R p).map ((lowerStar R p).map h) ≫
      (upperStarLowerStarAdjunction R p).counit.app _ =
    (upperStarLowerStarAdjunction R p).counit.app M ≫ h at hε
  rw [hε, Functor.map_comp, Category.assoc]

private theorem comparison_hom_eq
    (S : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj S] [IsCommMonObj S] {X U Y : Scheme.{u}}
    (p : U ⟶ X) (g : Y ⟶ X) (t : Y ⟶ U) (w : t ≫ p = g)
    (N : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj S X)) :
    (finiteEtaleTraceSheetComparison S p g t w).hom.app N =
      ((eqToIso (congrArg (upperStar S) w)).symm ≪≫ upperStarComp S t p).hom.app N := by
  exact congrArg (fun b ↦ b.hom.app N) (finiteEtaleTraceSheetComparison_eq S p g t w)

private theorem comparison_inv_eq
    (S : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj S] [IsCommMonObj S] {X U Y : Scheme.{u}}
    (p : U ⟶ X) (g : Y ⟶ X) (t : Y ⟶ U) (w : t ≫ p = g)
    (N : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj S X)) :
    (finiteEtaleTraceSheetComparison S p g t w).inv.app N =
      ((eqToIso (congrArg (upperStar S) w)).symm ≪≫ upperStarComp S t p).inv.app N := by
  exact congrArg (fun b ↦ b.inv.app N) (finiteEtaleTraceSheetComparison_eq S p g t w)

private theorem pushed_sheet
    {R S : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
    [MonObj R] [IsCommMonObj R] [MonObj S] [IsCommMonObj S]
    (a : R ⟶ S) [IsMonHom a] {X U Y : Scheme.{u}}
    (P : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj S X))
    (p : U ⟶ X) (g : Y ⟶ X) (t : Y ⟶ U) (w : t ≫ p = g)
    (M : Mod (Sheaf (Scheme.ProEt.topology U) Ab.{u + 1}) (condensedRingObj R U))
    (h : M ⟶ (Mod.comap (coefficientMap a U)).obj ((upperStar S p).obj P)) :
    (upperStar R g).map ((lowerStar R p).map h ≫
        (comapLowerStarIso a p).inv.app ((upperStar S p).obj P)) ≫
        (comapUpperStarIso a g).inv.app ((lowerStar S p).obj ((upperStar S p).obj P)) ≫
        (Mod.comap (coefficientMap a Y)).map
          ((finiteEtaleTraceSheetComparison S p g t w).hom.app
              ((lowerStar S p).obj ((upperStar S p).obj P)) ≫
            (upperStar S t).map
              ((upperStarLowerStarAdjunction S p).counit.app ((upperStar S p).obj P)) ≫
            (finiteEtaleTraceSheetComparison S p g t w).inv.app P) =
      ((eqToIso (congrArg (upperStar R) w)).symm ≪≫
          upperStarComp R t p).hom.app ((lowerStar R p).obj M) ≫
        (upperStar R t).map ((upperStarLowerStarAdjunction R p).counit.app M) ≫
        (upperStar R t).map h ≫
        (comapUpperStarIso a t).inv.app ((upperStar S p).obj P) ≫
        (Mod.comap (coefficientMap a Y)).map
          (((eqToIso (congrArg (upperStar S) w)).symm ≪≫
            upperStarComp S t p).inv.app P) := by
  rw [comparison_hom_eq, comparison_inv_eq]
  have hj := sheet_embedding_compatibility a p g t w M ((upperStar S p).obj P) h
  have hj' := congrArg (fun k ↦ k ≫ (Mod.comap (coefficientMap a Y)).map
    (((eqToIso (congrArg (upperStar S) w)).symm ≪≫
      upperStarComp S t p).inv.app P)) hj
  simpa only [Functor.map_comp, Category.assoc] using hj'

private theorem apply_chart_property
    {X U Y : Scheme.{u}} (p : U ⟶ X)
    (Q : ∀ (Y : Scheme.{u}) (g : Y ⟶ X) (d : ℕ)
      (t : Fin d → (Y ⟶ U)), (∀ j, t j ≫ p = g) → Prop)
    (h : ∀ c : FiniteEtaleModuleChart p, Q c.base c.map c.degree c.sheet c.over)
    (g : Y ⟶ X) [WeaklyEtale g] (d : ℕ)
    (t : Fin d → (Y ⟶ U)) (w : ∀ j, t j ≫ p = g)
    (hs : Nonempty (IsColimit (Cofan.mk (pullback p g)
      (fun j ↦ pullback.lift (t j) (𝟙 Y) (by simpa using w j))))) :
    Q Y g d t w := by
  exact h ⟨Y, g, inferInstance, d, t, w, hs⟩

private theorem pushed_trace_sum
    {R S : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
    [MonObj R] [IsCommMonObj R] [MonObj S] [IsCommMonObj S]
    (a : R ⟶ S) [IsMonHom a] {X U Y : Scheme.{u}}
    (P : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj S X))
    (p : U ⟶ X)
    (M : Mod (Sheaf (Scheme.ProEt.topology U) Ab.{u + 1}) (condensedRingObj R U))
    (h : M ⟶ (Mod.comap (coefficientMap a U)).obj ((upperStar S p).obj P))
    (τ : (lowerStar S p).obj ((upperStar S p).obj P) ⟶ P)
    (hτ : FiniteEtaleTraceFormula S p P τ)
    (g : Y ⟶ X) [WeaklyEtale g] (d : ℕ)
    (t : Fin d → (Y ⟶ U)) (w : ∀ j, t j ≫ p = g)
    (hs : Nonempty (IsColimit (Cofan.mk (pullback p g)
      (fun j ↦ pullback.lift (t j) (𝟙 Y) (by simpa using w j))))) :
    (upperStar R g).map ((lowerStar R p).map h ≫
        (comapLowerStarIso a p).inv.app ((upperStar S p).obj P) ≫
        (Mod.comap (coefficientMap a X)).map τ) ≫
        (comapUpperStarIso a g).inv.app P =
      ∑ j : Fin d,
        ((eqToIso (congrArg (upperStar R) (w j))).symm ≪≫
            upperStarComp R (t j) p).hom.app ((lowerStar R p).obj M) ≫
          (upperStar R (t j)).map ((upperStarLowerStarAdjunction R p).counit.app M) ≫
          (upperStar R (t j)).map h ≫
          (comapUpperStarIso a (t j)).inv.app ((upperStar S p).obj P) ≫
          (Mod.comap (coefficientMap a Y)).map
            (((eqToIso (congrArg (upperStar S) (w j))).symm ≪≫
              upperStarComp S (t j) p).inv.app P) := by
  classical
  have hτg := apply_chart_property p
    (fun Y g d t w ↦ (upperStar S g).map τ = finiteEtaleTraceSheetSum S p P g d t w)
    hτ g d t w hs
  rw [← Category.assoc ((lowerStar R p).map h)
    ((comapLowerStarIso a p).inv.app ((upperStar S p).obj P))
    ((Mod.comap (coefficientMap a X)).map τ), Functor.map_comp, Category.assoc]
  erw [(comapUpperStarIso a g).inv.naturality τ]
  change _ ≫ _ ≫ (Mod.comap (coefficientMap a Y)).map ((upperStar S g).map τ) = _
  rw [hτg, finiteEtaleTraceSheetSum, Functor.map_sum, Preadditive.comp_sum,
    Preadditive.comp_sum]
  apply Finset.sum_congr rfl
  intro j _
  exact pushed_sheet a P p g (t j) (w j) M h

section LatticeEquations
variable {R S : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
    [MonObj R] [IsCommMonObj R] [MonObj S] [IsCommMonObj S]
    (a : R ⟶ S) [IsMonHom a] {X U Y : Scheme.{u}}
    (P : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj S X))
    (p : U ⟶ X)
    (M : Mod (Sheaf (Scheme.ProEt.topology U) Ab.{u + 1}) (condensedRingObj R U))
    (e : (Mod.extendScalars (coefficientMap a U)).obj M ≅ (upperStar S p).obj P)

private theorem pushedEmbedding_eq :
    latticePushedEmbedding a X P p M e =
      (lowerStar R p).map (latticeIntegralEmbedding a X P p M e) ≫
        (comapLowerStarIso a p).inv.app ((upperStar S p).obj P) := by
  rfl

private theorem sheetEmbedding_eq (g : Y ⟶ X) (t : Y ⟶ U) (w : t ≫ p = g) :
    finiteEtaleLatticeSheetEmbedding a P p M e g t w =
      (upperStar R t).map (latticeIntegralEmbedding a X P p M e) ≫
        (comapUpperStarIso a t).inv.app ((upperStar S p).obj P) ≫
        (Mod.comap (coefficientMap a Y)).map
          (((eqToIso (congrArg (upperStar S) w)).symm ≪≫
            upperStarComp S t p).inv.app P) := by
  subst g
  unfold finiteEtaleLatticeSheetEmbedding
  simp only [eqToIso_refl, Iso.refl_symm, Iso.refl_trans]

private theorem trace_image_factorization
    (τ : (lowerStar S p).obj ((upperStar S p).obj P) ⟶ P) (g : Y ⟶ X) :
    (upperStar R g).map (factorThruImage
        (latticePushedEmbedding a X P p M e ≫
          (Mod.comap (coefficientMap a X)).map τ)) ≫
      finiteEtaleTraceImageEmbedding a P p M e τ g =
        (upperStar R g).map (latticePushedEmbedding a X P p M e ≫
          (Mod.comap (coefficientMap a X)).map τ) ≫
            (comapUpperStarIso a g).inv.app P := by
  unfold finiteEtaleTraceImageEmbedding
  exact map_image_factorization (upperStar R g) _ ((comapUpperStarIso a g).inv.app P)

private theorem trace_image_epi
    (τ : (lowerStar S p).obj ((upperStar S p).obj P) ⟶ P)
    (g : Y ⟶ X) [WeaklyEtale g] :
    Epi ((upperStar R g).map (factorThruImage
      (latticePushedEmbedding a X P p M e ≫
        (Mod.comap (coefficientMap a X)).map τ))) := by
  infer_instance

end LatticeEquations

private def integralSheetProjection
    (R : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj R] [IsCommMonObj R] {X U Y : Scheme.{u}}
    (p : U ⟶ X) (g : Y ⟶ X) (t : Y ⟶ U) (w : t ≫ p = g)
    (M : Mod (Sheaf (Scheme.ProEt.topology U) Ab.{u + 1}) (condensedRingObj R U)) :
    (upperStar R g).obj ((lowerStar R p).obj M) ⟶ (upperStar R t).obj M :=
  ((eqToIso (congrArg (upperStar R) w)).symm ≪≫ upperStarComp R t p).hom.app
      ((lowerStar R p).obj M) ≫
    (upperStar R t).map ((upperStarLowerStarAdjunction R p).counit.app M)

private theorem integralSheetProjection_eq
    (R : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj R] [IsCommMonObj R] {X U Y : Scheme.{u}}
    (p : U ⟶ X) (g : Y ⟶ X) (t : Y ⟶ U) (w : t ≫ p = g)
    (M : Mod (Sheaf (Scheme.ProEt.topology U) Ab.{u + 1}) (condensedRingObj R U)) :
    integralSheetProjection R p g t w M =
      ((eqToIso (congrArg (upperStar R) w)).symm ≪≫ upperStarComp R t p).hom.app
        ((lowerStar R p).obj M) ≫
      (upperStar R t).map ((upperStarLowerStarAdjunction R p).counit.app M) := by
  subst g
  simp only [integralSheetProjection, eqToIso_refl, Iso.refl_symm, Iso.refl_trans]

private theorem integral_sheet_product_isIso
    (R : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj R] [IsCommMonObj R] {X U Y : Scheme.{u}}
    (p : U ⟶ X) (g : Y ⟶ X) [WeaklyEtale g] (d : ℕ)
    (t : Fin d → (Y ⟶ U)) (w : ∀ j, t j ≫ p = g)
    (hs : Nonempty (IsColimit (Cofan.mk (pullback p g)
      (fun j ↦ pullback.lift (t j) (𝟙 Y) (by simpa using w j)))))
    (M : Mod (Sheaf (Scheme.ProEt.topology U) Ab.{u + 1}) (condensedRingObj R U)) :
    IsIso (Pi.lift (fun j ↦ integralSheetProjection R p g (t j) (w j) M)) := by
  -- Normalize the object family before comparing the chosen products.
  simpa only [Functor.id_obj, integralSheetProjection_eq] using
    (splitProEtaleModuleProductMap_isIso R p g d t w hs M)

private theorem integral_trace_sum
    {R S : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
    [MonObj R] [IsCommMonObj R] [MonObj S] [IsCommMonObj S]
    (a : R ⟶ S) [IsMonHom a] {X U Y : Scheme.{u}}
    (P : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj S X))
    (p : U ⟶ X)
    (M : Mod (Sheaf (Scheme.ProEt.topology U) Ab.{u + 1}) (condensedRingObj R U))
    (e : (Mod.extendScalars (coefficientMap a U)).obj M ≅ (upperStar S p).obj P)
    (τ : (lowerStar S p).obj ((upperStar S p).obj P) ⟶ P)
    (hτ : FiniteEtaleTraceFormula S p P τ)
    (g : Y ⟶ X) [WeaklyEtale g] (d : ℕ)
    (t : Fin d → (Y ⟶ U)) (w : ∀ j, t j ≫ p = g)
    (hs : Nonempty (IsColimit (Cofan.mk (pullback p g)
      (fun j ↦ pullback.lift (t j) (𝟙 Y) (by simpa using w j))))) :
    (upperStar R g).map (latticePushedEmbedding a X P p M e ≫
        (Mod.comap (coefficientMap a X)).map τ) ≫
        (comapUpperStarIso a g).inv.app P =
      ∑ j : Fin d,
        integralSheetProjection R p g (t j) (w j) M ≫
          finiteEtaleLatticeSheetEmbedding a P p M e g (t j) (w j) := by
  simpa only [pushedEmbedding_eq, sheetEmbedding_eq, integralSheetProjection_eq,
    Category.assoc]
    using pushed_trace_sum a P p M (latticeIntegralEmbedding a X P p M e) τ hτ
      g d t w hs

end TraceCompatibility

attribute [local irreducible] upperStar lowerStar upperStarComp upperStarLowerStarAdjunction
attribute [local irreducible] comapUpperStarIso comapLowerStarIso

/-- On an already specified splitting and in already specified embedded sheet
coordinates, the pulled-back categorical trace image has the sum of the sheet
ranges. Local freeness and existence of any chart are not hypotheses or conclusions.

Source: blueprint, stratified lattice trace proof, Local computation, paragraphs 1–2.
(blueprint: lem-sfb-finite-etale-trace-sheet-ranges)

Proof. The coefficient-restriction mate identity compares the actual counits,
and composition coherence compares their restrictions to each sheet. Naturality
then identifies the normalized integral trace map with the sum of the actual
sheet embeddings after the canonical integral sheet projections. The split
product comparison is invertible. Its inverse and the finite biproduct injections
insert arbitrary sheet sections, so the section range of this sum is exactly
the supremum of the specified sheet ranges.

The continuous lattice sum theorem identifies this supremum with continuous
functions into the algebraic sum lattice. In the target, sections whose supplied
coordinates take values in this lattice form a submodule sheaf: the coordinate
presentation identifies it naturally with continuous functions into the lattice.
The trace map factors through this sheaf. The cokernel of its inclusion therefore
kills the normalized trace map, and cancellation of the epimorphism in the pulled
and encoded categorical image factorization shows it also kills the image
inclusion. The kernel property factors the latter through the same submodule
sheaf. This gives one range inclusion; the trace factorization gives the reverse.
Neither the trace nor the embedding of M must be epic or monic. Rank zero and the
empty test scheme are included. -/
theorem finiteEtaleTrace_sheet_ranges
    (l : ℕ) [Fact l.Prime] (E : Type) [NormedField E]
    [NormedAlgebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    [TotallyDisconnectedSpace E] {X U Y : Scheme.{u}}
    (P : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousMapRingObj E) X))
    (p : U ⟶ X) [IsFinite p] [Etale p]
    (M : Mod (Sheaf (Scheme.ProEt.topology U) Ab.{u + 1})
      (condensedRingObj (integralCoeff l E) U))
    (e : (Mod.extendScalars (coefficientMap (integralScalarMap l E) U)).obj M ≅
      (upperStar (Profinite.continuousMapRingObj E) p).obj P)
    (τ : (lowerStar (Profinite.continuousMapRingObj E) p).obj
      ((upperStar (Profinite.continuousMapRingObj E) p).obj P) ⟶ P)
    (hτ : FiniteEtaleTraceFormula (Profinite.continuousMapRingObj E) p P τ)
    (g : Y ⟶ X) [WeaklyEtale g] (r d : ℕ) (hd : 0 < d)
    (t : Fin d → (Y ⟶ U)) (w : ∀ j, t j ≫ p = g)
    (hs : Nonempty (IsColimit (Cofan.mk (pullback p g)
      (fun j ↦ pullback.lift (t j) (𝟙 Y) (by simpa using w j)))))
    (L : Fin d → Submodule (continuousIntegers l E) (Fin r → E))
    (hL : ∀ j, ∃ b : Module.Basis (Fin r) (continuousIntegers l E) (L j),
      ∃ c : Module.Basis (Fin r) E (Fin r → E), ∀ i, (b i : Fin r → E) = c i)
    (c : ContinuousFunctionPresentation Y (continuousIntegers l E) (Fin r → E)
      ((Mod.comap (coefficientMap (integralScalarMap l E) Y)).obj
        ((upperStar (Profinite.continuousMapRingObj E) g).obj P)))
    (hc : ∀ (j : Fin d) (B : Y.ProEt),
      Set.range (fun x ↦ c.sections B
        (((continuousRingModuleEquivalence Y (continuousIntegers l E)).functor.map
          (finiteEtaleLatticeSheetEmbedding (integralScalarMap l E) P p M e
            g (t j) (w j))).val.app (op B) x)) =
        Set.range (continuousLatticeInclusion (continuousIntegers l E) (L j) B.left)) :
    ∀ B : Y.ProEt,
      Set.range (fun x ↦ c.sections B
        (((continuousRingModuleEquivalence Y (continuousIntegers l E)).functor.map
          (finiteEtaleTraceImageEmbedding (integralScalarMap l E) P p M e τ g)).val.app
            (op B) x)) =
        ↑(⨆ j, (continuousLatticeInclusion (continuousIntegers l E) (L j) B.left).range) := by
  -- Infer the intermediate objects from the actual maps to keep pullbacks folded.
  let : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
  let := trace_image_epi (R := integralCoeff l E)
    (S := Profinite.continuousMapRingObj E) (integralScalarMap l E) P p M e τ g
  exact presented_image_ranges (continuousIntegers l E) _ _ _ _
    ((upperStar (integralCoeff l E) g).map (factorThruImage
      (latticePushedEmbedding (integralScalarMap l E) X P p M e ≫
        (Mod.comap (coefficientMap (integralScalarMap l E) X)).map τ)))
    (finiteEtaleTraceImageEmbedding (integralScalarMap l E) P p M e τ g)
    (trace_image_factorization (R := integralCoeff l E)
      (S := Profinite.continuousMapRingObj E) (integralScalarMap l E) P p M e τ g) c L
    (presented_sum_ranges (continuousIntegers l E) _ _ _
      (fun j ↦ integralSheetProjection (integralCoeff l E) p g (t j) (w j) M)
      (integral_sheet_product_isIso (integralCoeff l E) p g d t w hs M)
      (fun j ↦ finiteEtaleLatticeSheetEmbedding (integralScalarMap l E) P p M e
        g (t j) (w j)) _
      (integral_trace_sum (R := integralCoeff l E) (S := Profinite.continuousMapRingObj E)
        (integralScalarMap l E) P p M e τ hτ g d t w hs) c L hc)
    (lattice_sum_section_ranges l E Y r d L hL)

end AlgebraicGeometry.ProEtale.CondensedRing
