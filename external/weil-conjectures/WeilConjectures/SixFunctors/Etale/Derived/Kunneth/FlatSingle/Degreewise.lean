/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.Kunneth.FlatSingle.HomologyFlat
public import WeilConjectures.SixFunctors.Etale.Derived.Kunneth.FlatSingle.TopHomology
public import WeilConjectures.SixFunctors.Etale.Derived.Kunneth.FlatSingle.DimensionShift
public import WeilConjectures.SixFunctors.Etale.Derived.Kunneth.FlatSingle.FilteredColimit
public import WeilConjectures.SixFunctors.Etale.Derived.Kunneth.FlatSingle.JacobsonTorsion
public import WeilConjectures.SixFunctors.Etale.Derived.TorAmplitudeResidue
public import WeilConjectures.SixFunctors.Etale.Derived.Kunneth.SingleReduction
public import WeilConjectures.ConstructibleSheaf.FilteredColimit
public import WeilConjectures.ConstructibleSheaf.FiniteMorphism
public import WeilConjectures.ConstructibleSheaf.Monoidal
public import WeilConjectures.ConstructibleSheaf.FiniteDirectImageKunneth
public import WeilConjectures.CategoryTheory.DerivedCategory.ConstructibleTorsion
public import WeilConjectures.Mathlib.CategoryTheory.Limits.Preserves.Shapes.Biproducts

/-!
# Dévissage of the degree-wise base change maps

Fix a commutative square `h ≫ f' = e ≫ g` with `h` quasi-compact and quasi-separated,
`p : X' ⟶ X` with `X` of finite type over a field, and a sheaf `𝓕` on `T` killed by the Jacobson
radical `J` of the finite ring `Λ`. Consider the degree-`q` base change maps
(`AlgebraicGeometry.Etale.tensorBaseChangeHomologyMap`)

`τ_q(𝓖) : Hᵠ(Lp^* 𝓖[0] ⊗ᴸ τ^{≤q} N) ⟶ Rᵠh_*(h^* p^* 𝓖 ⊗ e^* 𝓕)`, `N = Lf'^* Rg_* 𝓕[0]`,

natural in the sheaf `𝓖` on `X`. The source is `p^* 𝓖 ⊗ Hᵠ(τ^{≤q} N)`
(`AlgebraicGeometry.Etale.singleFunctorTensorRightHomologyIso`), a sheaf killed by `J`. If the
`τ_q` are isomorphisms at the sheaves `π_* Λ / J π_* Λ` for finite morphisms `π`, they are
isomorphisms at every sheaf `𝓖`
(`AlgebraicGeometry.Etale.isIso_tensorBaseChangeHomologyMap_app_of_cokernel_lowerStar`):

1. both sides only depend on `𝓖 / J 𝓖`, since they are right exact in `𝓖` and kill `J`;
2. `𝓖 / J 𝓖` is a filtered colimit of constructible sheaves killed by `J` (blueprint
   `lemma-finiteness-small-etale-topoi--1`), and both sides commute with filtered colimits;
3. a constructible sheaf killed by `J` embeds into a finite sum of sheaves `π_* M` with `M`
   killed by `J`, retracts of sums of copies of `π_* Λ / J π_* Λ`, with constructible cokernel
   killed by `J`; on short exact sequences of sheaves killed by `J`, the sources are exact (the
   tensor product over the semisimple ring `Λ / J`) and the targets form a long exact sequence,
   so dimension shifting (`CategoryTheory.isIso_app_of_dimensionShift`) applies.

This is the `𝔽_ℓ`-vector space case of the proof of blueprint `lemma-kunneth-field-coefficients--1`.
-/

@[expose] public section

universe u' u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor

section General

variable {C D : Type*} [Category C] [Category D]

/-- A natural transformation between additive functors which is an isomorphism at an object is an
isomorphism at the retracts of the finite sums of copies of it. The biproduct is taken with the
given `HasBiproduct` instance, so that no instance comparison is needed. -/
lemma CategoryTheory.NatTrans.isIso_app_of_retract_biproduct [Preadditive C] [Preadditive D]
    [HasFiniteBiproducts D] {S T : C ⥤ D} [S.Additive] [T.Additive] (τ : S ⟶ T) {A Z : C}
    {m : ℕ} {_ : HasBiproduct (fun _ : Fin m ↦ Z)} (r : Retract A (⨁ fun _ : Fin m ↦ Z))
    (hZ : IsIso (τ.app Z)) : IsIso (τ.app A) :=
  have := NatTrans.isIso_app_biproduct τ (fun _ : Fin m ↦ Z) fun _ ↦ hZ
  NatTrans.isIso_app_of_retract τ r

/-- Transport `IsIso (τ.app X)` along an equality `X = Y`. Used with `rfl` when `Y` is a
beta-redex: the kernel then compares the objects, not the components of `τ` at them. -/
private lemma CategoryTheory.NatTrans.isIso_app_of_isIso_app_of_eq {S T : C ⥤ D} {τ : S ⟶ T}
    {X Y : C} (hX : IsIso (τ.app X)) (h : X = Y) : IsIso (τ.app Y) :=
  h ▸ hX

/-- A natural transformation between functors preserving a colimit, which is an isomorphism on
the diagram, is an isomorphism at the colimit. -/
lemma CategoryTheory.NatTrans.isIso_app_of_isColimit_of_preservesColimit {J : Type*} [Category J]
    {S T : C ⥤ D} (τ : S ⟶ T) {F : J ⥤ C} {c : Cocone F} (hc : IsColimit c) [PreservesColimit F S]
    [PreservesColimit F T] (h : ∀ j, IsIso (τ.app (F.obj j))) : IsIso (τ.app c.pt) := by
  let hS := isColimitOfPreserves S hc
  let hT := isColimitOfPreserves T hc
  have : ∀ j, IsIso ((Functor.whiskerLeft F τ).app j) := h
  have : IsIso (Functor.whiskerLeft F τ) := NatIso.isIso_of_isIso_app _
  have e : τ.app c.pt = (hS.coconePointsIsoOfNatIso hT (asIso (Functor.whiskerLeft F τ))).hom :=
    hS.hom_ext fun j ↦ by
      rw [IsColimit.comp_coconePointsIsoOfNatIso_hom]
      exact τ.naturality (c.ι.app j)
  rw [e]
  infer_instance

/-- A functor preserving the cokernel of a morphism which it sends to zero sends the projection
to the cokernel to an isomorphism. -/
lemma CategoryTheory.Functor.isIso_map_cokernel_π_of_map_eq_zero [Abelian C] [Abelian D]
    (Φ : C ⥤ D) [Φ.PreservesZeroMorphisms] {A B : C} (f : A ⟶ B)
    [PreservesColimit (parallelPair f 0) Φ] (hf : Φ.map f = 0) :
    IsIso (Φ.map (cokernel.π f)) := by
  rw [← π_comp_cokernelComparison]
  have : IsIso (cokernel.π (Φ.map f)) :=
    CokernelCofork.IsColimit.isIso_π _ (colimit.isColimit _) hf
  infer_instance

end General

namespace AlgebraicGeometry

open Scheme

namespace Etale

section Smul

variable {Λ : Type (u + 1)} [CommRing Λ] {C D : Type*} [Category C] [Category D]

/-- The cokernel of `AlgebraicGeometry.Etale.smulDesc I A`, the quotient `A / I A`, is killed by
`I`. -/
lemma smul_id_cokernel_smulDesc [Abelian C] [HasFiniteBiproducts C] [Linear Λ C] (I : Ideal Λ)
    [Finite I] (A : C)
    {x : Λ} (hx : x ∈ I) : x • 𝟙 (cokernel (smulDesc I A)) = 0 := by
  rw [← cancel_epi (cokernel.π (smulDesc I A)), comp_zero, Linear.comp_smul, Category.comp_id,
    ← Category.id_comp (cokernel.π _), ← Linear.smul_comp]
  have : x • 𝟙 A = biproduct.ι (fun _ : I ↦ A) ⟨x, hx⟩ ≫ smulDesc I A := by
    simp [smulDesc]
  rw [this, Category.assoc, cokernel.condition, comp_zero]

/-- A quotient of an object killed by `I` is killed by `I`. -/
lemma smul_id_eq_zero_of_epi [Preadditive C] [Linear Λ C] {A B : C} (π : A ⟶ B) [Epi π]
    {x : Λ} (hA : x • 𝟙 A = 0) : x • 𝟙 B = 0 := by
  rw [← cancel_epi π, comp_zero, Linear.comp_smul, Category.comp_id,
    ← Category.id_comp π, ← Linear.smul_comp, hA, zero_comp]

/-- A subobject of an object killed by `I` is killed by `I`. -/
lemma smul_id_eq_zero_of_mono [Preadditive C] [Linear Λ C] {A B : C} (ι : A ⟶ B) [Mono ι]
    {x : Λ} (hB : x • 𝟙 B = 0) : x • 𝟙 A = 0 := by
  rw [← cancel_mono ι, zero_comp, Linear.smul_comp, Category.id_comp,
    ← Category.comp_id ι, ← Linear.comp_smul, hB, comp_zero]

/-- A retract of an object killed by `x` is killed by `x`. -/
lemma smul_id_eq_zero_of_retract [Preadditive C] [Linear Λ C] {A B : C} (r : Retract A B)
    {x : Λ} (hB : x • 𝟙 B = 0) : x • 𝟙 A = 0 :=
  calc x • 𝟙 A = r.i ≫ (x • 𝟙 B) ≫ r.r := by
        rw [Linear.smul_comp, Category.id_comp, Linear.comp_smul, r.retract]
    _ = 0 := by rw [hB, zero_comp, comp_zero]

/-- A biproduct of objects killed by `x` is killed by `x`. -/
lemma smul_id_biproduct_eq_zero [Preadditive C] [Linear Λ C] {ι : Type} [Finite ι]
    (f : ι → C) [HasBiproduct f] {x : Λ} (hf : ∀ i, x • 𝟙 (f i) = 0) :
    x • 𝟙 (⨁ f) = 0 := by
  refine biproduct.hom_ext _ _ fun i ↦ ?_
  rw [zero_comp, Linear.smul_comp, Category.id_comp, ← Category.comp_id (biproduct.π f i),
    ← Linear.comp_smul, hf i, comp_zero]

/-- A functor sending the multiplications by the elements of `I` on `A` to zero sends
`AlgebraicGeometry.Etale.smulDesc I A` to zero. -/
lemma map_smulDesc_eq_zero [Preadditive C] [Preadditive D] [Linear Λ C]
    [HasFiniteBiproducts C] (Φ : C ⥤ D) [Φ.Additive] (I : Ideal Λ) [Finite I] (A : C)
    (hΦ : ∀ x ∈ I, Φ.map (x • 𝟙 A) = 0) : Φ.map (smulDesc I A) = 0 := by
  rw [← cancel_epi (Φ.mapBiproduct (fun _ : I ↦ A)).inv, comp_zero]
  refine biproduct.hom_ext' _ _ fun x ↦ ?_
  rw [Functor.mapBiproduct_inv, biproduct.ι_desc_assoc, ← Φ.map_comp, smulDesc,
    biproduct.ι_desc, hΦ x x.2, comp_zero]

end Smul

section Generic

/-! ### Constructions for a general coefficient category -/

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A]
  {X X' S' T Y : Scheme.{u}} (p : X' ⟶ X) (h : Y ⟶ X') (e : Y ⟶ T) (f' : X' ⟶ S') (g : T ⟶ S')
  (w : h ≫ f' = e ≫ g) (𝓕 : Sheaf T.smallEtaleTopology A)

/-- The sheaf `Hᵠ(τ^{≤q} N)` on `X'`, `N = Lf'^* Rg_* 𝓕[0]`. -/
noncomputable abbrev tensorBaseChangeHomologySheaf (q : ℤ) : Sheaf X'.smallEtaleTopology A :=
  (DerivedCategory.homologyFunctor _ q).obj
    ((DerivedCategory.TStructure.t.truncLE q).obj (tensorBaseChangeComplex A f' g 𝓕))

/-- The source of the degree-`q` base change map is `𝓖 ↦ p^* 𝓖 ⊗ Hᵠ(τ^{≤q} N)`. -/
noncomputable def tensorBaseChangeHomologySourceIso (q : ℤ) :
    tensorBaseChangeHomologySource A p f' g 𝓕 q ≅
      (p)^*[A] ⋙ tensorRight (tensorBaseChangeHomologySheaf A f' g 𝓕 q) :=
  let M := (DerivedCategory.TStructure.t.truncLE q).obj (tensorBaseChangeComplex A f' g 𝓕)
  let sX := DerivedCategory.singleFunctor (Sheaf X.smallEtaleTopology A) 0
  let sX' := DerivedCategory.singleFunctor (Sheaf X'.smallEtaleTopology A) 0
  let rest := tensorRight M ⋙ DerivedCategory.homologyFunctor (Sheaf X'.smallEtaleTopology A) q
  (Functor.associator sX L((p)^*[A]) rest).symm ≪≫
    Functor.isoWhiskerRight (singleFunctorCompLeftDerivedUpperStarIso A p) rest ≪≫
    Functor.associator (p)^*[A] sX' rest ≪≫
    Functor.isoWhiskerLeft (p)^*[A] (singleFunctorTensorRightHomologyIso M q)

/-- The complex `N = Lf'^* Rg_* 𝓕[0]` is concentrated in degrees `≥ 0`. -/
instance isGE_tensorBaseChangeComplex : (tensorBaseChangeComplex A f' g 𝓕).IsGE 0 := by
  have : (R((g)_*[A]).obj ((DerivedCategory.singleFunctor _ 0).obj 𝓕)).IsGE 0 :=
    ((g)_*[A]).isGE_rightDerivedFunctor_obj _ 0
  exact isGE_leftDerivedUpperStar_obj A f' _ 0

/-- The sheaf `Hᵠ(τ^{≤q} N)` is isomorphic to `Hᵠ(N)`. -/
noncomputable def tensorBaseChangeHomologySheafIso (q : ℤ) :
    tensorBaseChangeHomologySheaf A f' g 𝓕 q ≅
      (DerivedCategory.homologyFunctor _ q).obj (tensorBaseChangeComplex A f' g 𝓕) :=
  have := DerivedCategory.isIso_homologyFunctor_map_truncLTι_app
    (tensorBaseChangeComplex A f' g 𝓕) (q + 1) q (by lia)
  have : IsIso ((DerivedCategory.homologyFunctor _ q).map
      ((DerivedCategory.TStructure.t.truncLEι q).app (tensorBaseChangeComplex A f' g 𝓕))) := by
    rw [← DerivedCategory.TStructure.t.truncLEIsoTruncLT_hom_ι_app q (q + 1) rfl, Functor.map_comp]
    infer_instance
  asIso ((DerivedCategory.homologyFunctor _ q).map
    ((DerivedCategory.TStructure.t.truncLEι q).app (tensorBaseChangeComplex A f' g 𝓕)))

/-- The sheaf `Hᵠ(τ^{≤q} N)` vanishes in negative degrees. -/
lemma isZero_tensorBaseChangeHomologySheaf {q : ℤ} (hq : q < 0) :
    IsZero (tensorBaseChangeHomologySheaf A f' g 𝓕 q) :=
  ((tensorBaseChangeComplex A f' g 𝓕).isZero_of_isGE 0 q hq).of_iso
    (tensorBaseChangeHomologySheafIso A f' g 𝓕 q)

/-- The source `p^* 𝓖 ⊗ Hᵠ(τ^{≤q} N)` vanishes in negative degrees. -/
lemma isZero_tensorBaseChangeHomologySource'_obj {q : ℤ} (hq : q < 0)
    (𝓖 : Sheaf X.smallEtaleTopology A) :
    IsZero (((p)^*[A] ⋙ tensorRight (tensorBaseChangeHomologySheaf A f' g 𝓕 q)).obj 𝓖) :=
  (IsZero.iff_id_eq_zero _).2 (by
    dsimp
    rw [← MonoidalCategory.whiskerLeft_id,
      (isZero_tensorBaseChangeHomologySheaf A f' g 𝓕 hq).eq_of_src (𝟙 _) 0,
      MonoidalPreadditive.whiskerLeft_zero])

omit [MonoidalPreadditive A] [Abelian.HasFunctorialFlatResolution A] in
/-- The target `Rᵠh_*(h^* p^* 𝓖 ⊗ e^* 𝓕)` vanishes in negative degrees. -/
lemma isZero_tensorBaseChangeHomologyTarget_obj {q : ℤ} (hq : q < 0)
    (𝓖 : Sheaf X.smallEtaleTopology A) :
    IsZero ((tensorBaseChangeHomologyTarget A p h e 𝓕 q).obj 𝓖) := by
  have := ((h)_*[A]).isGE_rightDerivedFunctor_obj
    ((DerivedCategory.singleFunctor _ 0).obj
      ((tensorBaseChangeHomologyTargetSheaf A p h e 𝓕).obj 𝓖)) 0
  exact (R((h)_*[A]).obj ((DerivedCategory.singleFunctor _ 0).obj
      ((tensorBaseChangeHomologyTargetSheaf A p h e 𝓕).obj 𝓖))).isZero_of_isGE 0 q hq

omit [Abelian.HasFunctorialFlatResolution A] in
/-- The functor `𝓖 ↦ p^* 𝓖 ⊗ H` is additive. -/
instance additive_upperStar_comp_tensorRight (H : Sheaf X'.smallEtaleTopology A) :
    ((p)^*[A] ⋙ tensorRight H).Additive :=
  inferInstance

instance additive_tensorBaseChangeHomologyTarget (q : ℤ) :
    (tensorBaseChangeHomologyTarget A p h e 𝓕 q).Additive :=
  inferInstanceAs (tensorBaseChangeHomologyTargetSheaf A p h e 𝓕 ⋙
    higherDirectImageFunctor A h q).Additive

variable [Etale.UpperStarPreservesFlat A]

/-- The degree-`q` base change map with the source `p^* 𝓖 ⊗ Hᵠ(τ^{≤q} N)`. -/
noncomputable def tensorBaseChangeHomologyMap' (q : ℤ) :
    (p)^*[A] ⋙ tensorRight (tensorBaseChangeHomologySheaf A f' g 𝓕 q) ⟶
      tensorBaseChangeHomologyTarget A p h e 𝓕 q :=
  (tensorBaseChangeHomologySourceIso A p f' g 𝓕 q).inv ≫
    tensorBaseChangeHomologyMap A p h e f' g w 𝓕 q

lemma isIso_tensorBaseChangeHomologyMap'_app_iff (q : ℤ) (𝓖 : Sheaf X.smallEtaleTopology A) :
    IsIso ((tensorBaseChangeHomologyMap' A p h e f' g w 𝓕 q).app 𝓖) ↔
      IsIso ((tensorBaseChangeHomologyMap A p h e f' g w 𝓕 q).app 𝓖) := by
  rw [tensorBaseChangeHomologyMap', NatTrans.comp_app, isIso_comp_left_iff]

/-- The degree-wise base change maps are isomorphisms at finite sums of sheaves at which they are
isomorphisms. -/
lemma isIso_tensorBaseChangeHomologyMap'_app_biproduct (q : ℤ) {r : ℕ}
    (F : Fin r → Sheaf X.smallEtaleTopology A) {_ : HasBiproduct F}
    (hF : ∀ i, IsIso ((tensorBaseChangeHomologyMap' A p h e f' g w 𝓕 q).app (F i))) :
    IsIso ((tensorBaseChangeHomologyMap' A p h e f' g w 𝓕 q).app (⨁ F)) := by
  have : HasFiniteBiproducts (Sheaf X'.smallEtaleTopology A) := Abelian.hasFiniteBiproducts
  exact NatTrans.isIso_app_biproduct _ _ hF

/-- The degree-wise base change map is an isomorphism in negative degrees. -/
lemma isIso_tensorBaseChangeHomologyMap'_app_of_neg {q : ℤ} (hq : q < 0)
    (𝓖 : Sheaf X.smallEtaleTopology A) :
    IsIso ((tensorBaseChangeHomologyMap' A p h e f' g w 𝓕 q).app 𝓖) :=
  ⟨0, (isZero_tensorBaseChangeHomologySource'_obj A p f' g 𝓕 hq 𝓖).eq_of_src _ _,
    (isZero_tensorBaseChangeHomologyTarget_obj A p h e 𝓕 hq 𝓖).eq_of_src _ _⟩

omit [Abelian.HasFunctorialFlatResolution A] [Etale.UpperStarPreservesFlat A] in
/-- If `𝓖 ↦ h^* p^* 𝓖 ⊗ e^* 𝓕` sends a short exact sequence to a short exact sequence, the
functors `𝓖 ↦ Rᵠh_*(h^* p^* 𝓖 ⊗ e^* 𝓕)` form a long exact sequence on it. -/
lemma exists_δ_tensorBaseChangeHomologyTarget (S : ShortComplex (Sheaf X.smallEtaleTopology A))
    (hS : (S.map (tensorBaseChangeHomologyTargetSheaf A p h e 𝓕)).ShortExact) (q : ℤ) :
    ∃ (δ : (tensorBaseChangeHomologyTarget A p h e 𝓕 (q - 1)).obj S.X₃ ⟶
        (tensorBaseChangeHomologyTarget A p h e 𝓕 q).obj S.X₁)
      (hδ : δ ≫ (tensorBaseChangeHomologyTarget A p h e 𝓕 q).map S.f = 0),
      (tensorBaseChangeHomologyTarget A p h e 𝓕 (q - 1)).map S.g ≫ δ = 0 ∧
        (ShortComplex.mk δ _ hδ).Exact := by
  let T := R((h)_*[A]).mapTriangle.obj hS.singleTriangle
  have hT : T ∈ distTriang _ := R((h)_*[A]).map_distinguished _ hS.singleTriangle_distinguished
  exact ⟨DerivedCategory.HomologySequence.δ T (q - 1) q (by lia),
    DerivedCategory.HomologySequence.δ_comp T hT (q - 1) q (by lia),
    DerivedCategory.HomologySequence.comp_δ T hT (q - 1) q (by lia),
    DerivedCategory.HomologySequence.exact₁ T hT (q - 1) q (by lia)⟩

end Generic
section ModuleCat

/-! ### Coefficients in a finite ring -/

-- The generic constructions above use the preadditive structure of `A` coming from `Abelian A`
-- and the braiding coming from `SymmetricCategory A`; using the same ones for `ModuleCat Λ` avoids
-- expensive comparisons of the two.
attribute [local instance 10000] Abelian.toPreadditive SymmetricCategory.toBraidedCategory

variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]

omit [Finite Λ] in
/-- Tensoring with a sheaf killed by `x` kills the multiplication by `x`. -/
lemma whiskerRight_smul_id_eq_zero {Z : Scheme.{u}}
    (B H : Sheaf Z.smallEtaleTopology (ModuleCat.{u + 1} Λ)) {x : Λ} (hH : x • 𝟙 H = 0) :
    (x • 𝟙 B) ▷ H = 0 := by
  rw [MonoidalLinear.smul_whiskerRight, id_whiskerRight, ← MonoidalCategory.whiskerLeft_id,
    ← MonoidalLinear.whiskerLeft_smul, hH, MonoidalPreadditive.whiskerLeft_zero]

omit [Finite Λ] in
/-- A functor `Λ`-linear on morphisms kills the multiplications by elements killing an object. -/
lemma map_smul_id_eq_zero {C D : Type*} [Category C] [Category D] [Preadditive C]
    [Preadditive D] [Linear Λ C] [Linear Λ D] (F : C ⥤ D) [F.Additive] [F.Linear Λ] {A : C}
    {x : Λ} (hA : x • 𝟙 A = 0) : x • 𝟙 (F.obj A) = 0 := by
  rw [← CategoryTheory.Functor.map_id, ← Functor.map_smul, hA, Functor.map_zero]

variable {X X' S' T Y : Scheme.{u}} (p : X' ⟶ X) (h : Y ⟶ X') (e : Y ⟶ T) (f' : X' ⟶ S')
  (g : T ⟶ S') (w : h ≫ f' = e ≫ g) (𝓕 : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ))

omit [Finite Λ] in
variable {𝓕} in
/-- The sheaf `Hᵠ(τ^{≤q} N)` is killed by every element killing `𝓕`. -/
lemma smul_id_tensorBaseChangeHomologySheaf {x : Λ} (hx : x • 𝟙 𝓕 = 0) (q : ℤ) :
    x • 𝟙 (tensorBaseChangeHomologySheaf (ModuleCat.{u + 1} Λ) f' g 𝓕 q) = 0 := by
  have hN : x • 𝟙 (tensorBaseChangeComplex (ModuleCat.{u + 1} Λ) f' g 𝓕) = 0 :=
    map_smul_id_eq_zero Λ L((f')^*[ModuleCat.{u + 1} Λ])
      (map_smul_id_eq_zero Λ R((g)_*[ModuleCat.{u + 1} Λ])
        (map_smul_id_eq_zero Λ (DerivedCategory.singleFunctor _ 0) hx))
  exact smul_id_eq_zero_of_mono
    (tensorBaseChangeHomologySheafIso (ModuleCat.{u + 1} Λ) f' g 𝓕 q).hom
    (map_smul_id_eq_zero Λ (DerivedCategory.homologyFunctor _ q) hN)

/-- On short exact sequences of sheaves on `X` whose middle term is killed by the Jacobson radical,
the functor `𝓖 ↦ p^* 𝓖 ⊗ H` is exact, for any sheaf `H` on `X'`. -/
lemma exact_upperStar_tensorRight (H : Sheaf X'.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (S : ShortComplex (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))) (hS : S.ShortExact)
    (hS₂ : ∀ x ∈ Ring.jacobson Λ, x • 𝟙 S.X₂ = 0) :
    Mono (((p)^*[ModuleCat.{u + 1} Λ] ⋙ tensorRight H).map S.f) ∧
      Epi (((p)^*[ModuleCat.{u + 1} Λ] ⋙ tensorRight H).map S.g) ∧
      (S.map ((p)^*[ModuleCat.{u + 1} Λ] ⋙ tensorRight H)).Exact := by
  have := hS.mono_f
  have := hS.epi_g
  have := preservesFiniteColimits_tensorRight H
  refine ⟨?_, inferInstance, hS.exact.map_of_epi_of_preservesCokernel _ hS.epi_g inferInstance⟩
  exact Sheaf.mono_whiskerRight_of_smul_eq_zero_of_ideal (Ring.jacobson Λ)
    ((p)^*[ModuleCat.{u + 1} Λ].map S.f) (fun x hx ↦ map_smul_id_eq_zero Λ _ (hS₂ x hx)) H

/-- On short exact sequences of sheaves on `X` whose middle term is killed by the Jacobson radical,
the functor `𝓖 ↦ h^* p^* 𝓖 ⊗ e^* 𝓕` is exact. -/
lemma shortExact_map_tensorBaseChangeHomologyTargetSheaf
    (S : ShortComplex (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))) (hS : S.ShortExact)
    (hS₂ : ∀ x ∈ Ring.jacobson Λ, x • 𝟙 S.X₂ = 0) :
    (S.map (tensorBaseChangeHomologyTargetSheaf (ModuleCat.{u + 1} Λ) p h e 𝓕)).ShortExact := by
  have := hS.mono_f
  have := hS.epi_g
  have := preservesFiniteColimits_tensorRight ((e)^*[ModuleCat.{u + 1} Λ].obj 𝓕)
  have : Mono (S.map (tensorBaseChangeHomologyTargetSheaf (ModuleCat.{u + 1} Λ) p h e 𝓕)).f :=
    Sheaf.mono_whiskerRight_of_smul_eq_zero_of_ideal (Ring.jacobson Λ)
      ((h)^*[ModuleCat.{u + 1} Λ].map ((p)^*[ModuleCat.{u + 1} Λ].map S.f))
      (fun x hx ↦ map_smul_id_eq_zero Λ _ (map_smul_id_eq_zero Λ _ (hS₂ x hx))) _
  have : Epi (S.map (tensorBaseChangeHomologyTargetSheaf (ModuleCat.{u + 1} Λ) p h e 𝓕)).g :=
    inferInstanceAs (Epi ((tensorBaseChangeHomologyTargetSheaf (ModuleCat.{u + 1} Λ) p h e 𝓕).map
      S.g))
  exact ⟨hS.exact.map_of_epi_of_preservesCokernel _ hS.epi_g inferInstance⟩
/-- The degree-`q` base change map at a sheaf `𝓖` is an isomorphism if and only if it is one at
`𝓖 / J 𝓖`: both sides are right exact in `𝓖` and kill the Jacobson radical `J`. -/
lemma isIso_tensorBaseChangeHomologyMap_app_iff_cokernel_smulDesc
    (h𝓕 : ∀ x ∈ Ring.jacobson Λ, x • 𝟙 𝓕 = 0) (q : ℤ)
    (𝓖 : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    IsIso ((tensorBaseChangeHomologyMap (ModuleCat.{u + 1} Λ) p h e f' g w 𝓕 q).app 𝓖) ↔
      IsIso ((tensorBaseChangeHomologyMap (ModuleCat.{u + 1} Λ) p h e f' g w 𝓕 q).app
        (cokernel (smulDesc (Ring.jacobson Λ) 𝓖))) := by
  rw [← isIso_tensorBaseChangeHomologyMap'_app_iff, ← isIso_tensorBaseChangeHomologyMap'_app_iff]
  let τ := tensorBaseChangeHomologyMap' (ModuleCat.{u + 1} Λ) p h e f' g w 𝓕 q
  let π := cokernel.π (smulDesc (Ring.jacobson Λ) 𝓖)
  let Φ := (p)^*[ModuleCat.{u + 1} Λ] ⋙
    tensorRight (tensorBaseChangeHomologySheaf (ModuleCat.{u + 1} Λ) f' g 𝓕 q)
  let Ψ := tensorBaseChangeHomologyTargetSheaf (ModuleCat.{u + 1} Λ) p h e 𝓕
  have := preservesFiniteColimits_tensorRight
    (tensorBaseChangeHomologySheaf (ModuleCat.{u + 1} Λ) f' g 𝓕 q)
  have := preservesFiniteColimits_tensorRight ((e)^*[ModuleCat.{u + 1} Λ].obj 𝓕)
  have hΦ : IsIso (Φ.map π) := Functor.isIso_map_cokernel_π_of_map_eq_zero Φ _
    (map_smulDesc_eq_zero Φ _ _ fun x hx ↦ by
      change (p)^*[ModuleCat.{u + 1} Λ].map (x • 𝟙 𝓖) ▷ _ = 0
      rw [Functor.map_smul, CategoryTheory.Functor.map_id]
      exact whiskerRight_smul_id_eq_zero Λ _ _
        (smul_id_tensorBaseChangeHomologySheaf Λ f' g (h𝓕 x hx) q))
  have hΨ : IsIso (Ψ.map π) := Functor.isIso_map_cokernel_π_of_map_eq_zero Ψ _
    (map_smulDesc_eq_zero Ψ _ _ fun x hx ↦ by
      change (h)^*[ModuleCat.{u + 1} Λ].map ((p)^*[ModuleCat.{u + 1} Λ].map (x • 𝟙 𝓖)) ▷ _ = 0
      rw [Functor.map_smul, CategoryTheory.Functor.map_id, Functor.map_smul,
        CategoryTheory.Functor.map_id]
      exact whiskerRight_smul_id_eq_zero Λ _ _ (map_smul_id_eq_zero Λ _ (h𝓕 x hx)))
  have hT : IsIso ((tensorBaseChangeHomologyTarget (ModuleCat.{u + 1} Λ) p h e 𝓕 q).map π) :=
    inferInstanceAs (IsIso ((higherDirectImageFunctor (ModuleCat.{u + 1} Λ) h q).map (Ψ.map π)))
  have hn := τ.naturality π
  constructor
  · intro _
    have : IsIso (Φ.map π ≫ τ.app _) := by rw [hn]; infer_instance
    exact IsIso.of_isIso_comp_left (Φ.map π) _
  · intro _
    have : IsIso (τ.app 𝓖 ≫
        (tensorBaseChangeHomologyTarget (ModuleCat.{u + 1} Λ) p h e 𝓕 q).map π) := by
      rw [← hn]; infer_instance
    exact IsIso.of_isIso_comp_right _
      ((tensorBaseChangeHomologyTarget (ModuleCat.{u + 1} Λ) p h e 𝓕 q).map π)

variable {Λ} in
/-- A sheaf `π_* M`, for `π` finite and `M` finite killed by the Jacobson radical `J`, is killed by
`J`. -/
lemma smul_id_lowerStar_constantSheaf {Z : Scheme.{u}} (π : Z ⟶ X) [IsFinite π]
    (M : ModuleCat.{u + 1} Λ) [Finite M] (hM : ∀ x ∈ Ring.jacobson Λ, x • 𝟙 M = 0) {x : Λ}
    (hx : x ∈ Ring.jacobson Λ) :
    x • 𝟙 ((π)_*[ModuleCat.{u + 1} Λ].obj
      ((constantSheaf Z.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj M)) = 0 := by
  obtain ⟨m, ⟨r⟩⟩ := exists_retract_lowerStar_constantSheaf_of_smul_eq_zero Λ π M hM
  exact smul_id_eq_zero_of_retract r
    (smul_id_biproduct_eq_zero _ fun _ ↦ smul_id_cokernel_smulDesc _ _ hx)

/-- If the degree-wise base change map is an isomorphism at `π_* Λ / J π_* Λ`, it is an
isomorphism at `π_* M` for every finite module `M` killed by `J`. -/
lemma isIso_tensorBaseChangeHomologyMap'_app_lowerStar_constantSheaf {Z : Scheme.{u}}
    (π : Z ⟶ X) [IsFinite π] (q : ℤ)
    (hgood : IsIso ((tensorBaseChangeHomologyMap (ModuleCat.{u + 1} Λ) p h e f' g w 𝓕 q).app
        (cokernel (smulDesc (Ring.jacobson Λ) ((π)_*[ModuleCat.{u + 1} Λ].obj (𝟙_ _))))))
    (M : ModuleCat.{u + 1} Λ) [Finite M] (hM : ∀ x ∈ Ring.jacobson Λ, x • 𝟙 M = 0) :
    IsIso ((tensorBaseChangeHomologyMap' (ModuleCat.{u + 1} Λ) p h e f' g w 𝓕 q).app
      ((π)_*[ModuleCat.{u + 1} Λ].obj
        ((constantSheaf Z.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj M))) := by
  obtain ⟨m, ⟨r⟩⟩ := exists_retract_lowerStar_constantSheaf_of_smul_eq_zero Λ π M hM
  have := (isIso_tensorBaseChangeHomologyMap'_app_iff (ModuleCat.{u + 1} Λ) p h e f' g w 𝓕 q
    _).2 hgood
  exact NatTrans.isIso_app_of_retract_biproduct _ r this

variable {Λ} in
/-- A finite sum of sheaves `πᵢ_* Mᵢ`, `πᵢ` finite and `Mᵢ` finite killed by `J`, is killed by `J`.
-/
lemma smul_id_biproduct_lowerStar_constantSheaf {r : ℕ} {Z : Fin r → Scheme.{u}}
    (π : ∀ i, Z i ⟶ X) [∀ i, IsFinite (π i)] (M : Fin r → ModuleCat.{u + 1} Λ)
    [∀ i, Finite (M i)] (hM : ∀ i, ∀ x ∈ Ring.jacobson Λ, x • 𝟙 (M i) = 0) {x : Λ}
    (hx : x ∈ Ring.jacobson Λ) :
    x • 𝟙 (⨁ fun i ↦ (π i)_*[ModuleCat.{u + 1} Λ].obj
      ((constantSheaf (Z i).smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj (M i))) = 0 :=
  smul_id_biproduct_eq_zero _ fun i ↦ smul_id_lowerStar_constantSheaf (π i) (M i) (hM i) hx

/-- The degree-wise base change maps are isomorphisms at finite sums of sheaves `πᵢ_* Mᵢ`. -/
lemma isIso_tensorBaseChangeHomologyMap'_app_biproduct_lowerStar_constantSheaf {r : ℕ}
    {Z : Fin r → Scheme.{u}} (π : ∀ i, Z i ⟶ X) [∀ i, IsFinite (π i)] (q : ℤ)
    (hgood : ∀ i, IsIso ((tensorBaseChangeHomologyMap (ModuleCat.{u + 1} Λ) p h e f' g w 𝓕 q).app
        (cokernel (smulDesc (Ring.jacobson Λ) ((π i)_*[ModuleCat.{u + 1} Λ].obj (𝟙_ _))))))
    (M : Fin r → ModuleCat.{u + 1} Λ) [∀ i, Finite (M i)]
    (hM : ∀ i, ∀ x ∈ Ring.jacobson Λ, x • 𝟙 (M i) = 0) :
    IsIso ((tensorBaseChangeHomologyMap' (ModuleCat.{u + 1} Λ) p h e f' g w 𝓕 q).app
      (⨁ fun i ↦ (π i)_*[ModuleCat.{u + 1} Λ].obj
        ((constantSheaf (Z i).smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj (M i)))) := by
  -- The hypothesis of `isIso_tensorBaseChangeHomologyMap'_app_biproduct` is about the summand
  -- `(fun i ↦ π_i_* M_i) i`; the kernel compares `τ.app` of it with `τ.app (π_i_* M_i)` by
  -- unfolding `τ`, so the summand is transported along `rfl` at the level of objects instead.
  exact isIso_tensorBaseChangeHomologyMap'_app_biproduct (ModuleCat.{u + 1} Λ) p h e f' g w 𝓕 q
    (fun i ↦ (π i)_*[ModuleCat.{u + 1} Λ].obj
      ((constantSheaf (Z i).smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj (M i))) fun i ↦
    NatTrans.isIso_app_of_isIso_app_of_eq
      (isIso_tensorBaseChangeHomologyMap'_app_lowerStar_constantSheaf Λ p h e f' g w 𝓕 (π i) q
        (hgood i) (M i) (hM i))
      (Y := (fun i ↦ (π i)_*[ModuleCat.{u + 1} Λ].obj
        ((constantSheaf (Z i).smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj (M i))) i) rfl

variable {Λ} in
/-- A finite sum of sheaves `πᵢ_* Mᵢ`, `πᵢ` finite and `Mᵢ` finite, on a Noetherian scheme, is
constructible. -/
lemma isConstructibleSheaf_biproduct_lowerStar_constantSheaf [IsNoetherian X] {r : ℕ}
    {Z : Fin r → Scheme.{u}} (π : ∀ i, Z i ⟶ X) [∀ i, IsFinite (π i)]
    (M : Fin r → ModuleCat.{u + 1} Λ) [∀ i, Finite (M i)] :
    IsConstructibleSheaf (⨁ fun i ↦ (π i)_*[ModuleCat.{u + 1} Λ].obj
      ((constantSheaf (Z i).smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj (M i))) := by
  have (i : Fin r) : IsConstructibleSheaf ((π i)_*[ModuleCat.{u + 1} Λ].obj
      ((constantSheaf (Z i).smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj (M i))) := by
    have : Module.Finite Λ (M i) := Module.Finite.of_finite
    have := Scheme.isConstructibleSheaf_constantSheaf (X := Z i) (M i)
    exact Scheme.IsConstructibleSheaf.lowerStar_of_isFinite (π i) _
  exact IsConstructibleSheaf.biproduct _

/-- Dimension shifting: if the degree-wise base change maps are isomorphisms at the sheaves
`π_* Λ / J π_* Λ` for finite morphisms `π`, they are isomorphisms at every constructible sheaf
killed by the Jacobson radical `J`, on `X` of finite type over a field. -/
theorem isIso_tensorBaseChangeHomologyMap_app_of_isConstructibleSheaf {K : Type u} [Field K]
    (a : X ⟶ Spec (.of K)) [LocallyOfFiniteType a] [QuasiCompact a]
    (hgood : ∀ {Xᵢ : Scheme.{u}} (π : Xᵢ ⟶ X) [IsFinite π] (q : ℤ),
      IsIso ((tensorBaseChangeHomologyMap (ModuleCat.{u + 1} Λ) p h e f' g w 𝓕 q).app
        (cokernel (smulDesc (Ring.jacobson Λ) ((π)_*[ModuleCat.{u + 1} Λ].obj (𝟙_ _))))))
    (q : ℤ) (B : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) [IsConstructibleSheaf B]
    (hB : ∀ x ∈ Ring.jacobson Λ, x • 𝟙 B = 0) :
    IsIso ((tensorBaseChangeHomologyMap (ModuleCat.{u + 1} Λ) p h e f' g w 𝓕 q).app B) := by
  have := QuasiCompact.compactSpace_of_compactSpace a
  have : IsNoetherian X := { __ := LocallyOfFiniteType.isLocallyNoetherian a }
  refine (isIso_tensorBaseChangeHomologyMap'_app_iff _ p h e f' g w 𝓕 q B).1 ?_
  refine isIso_app_of_dimensionShift (D := Sheaf X'.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (fun A ↦ IsConstructibleSheaf A ∧ ∀ x ∈ Ring.jacobson Λ, x • 𝟙 A = 0)
    (fun A ↦ (∀ x ∈ Ring.jacobson Λ, x • 𝟙 A = 0) ∧ ∀ q, IsIso
      ((tensorBaseChangeHomologyMap' (ModuleCat.{u + 1} Λ) p h e f' g w 𝓕 q).app A))
    (fun q ↦ (p)^*[ModuleCat.{u + 1} Λ] ⋙
      tensorRight (tensorBaseChangeHomologySheaf (ModuleCat.{u + 1} Λ) f' g 𝓕 q))
    (fun q ↦ tensorBaseChangeHomologyTarget (ModuleCat.{u + 1} Λ) p h e 𝓕 q)
    (tensorBaseChangeHomologyMap' (ModuleCat.{u + 1} Λ) p h e f' g w 𝓕)
    (fun q hq A _ ↦ isIso_tensorBaseChangeHomologyMap'_app_of_neg _ p h e f' g w 𝓕 hq A)
    (fun q A hA ↦ hA.2 q) ?_ q B ⟨inferInstance, hB⟩
  rintro A ⟨hAc, hAJ⟩
  obtain ⟨r, Y, π, hπfin, M, hMfin, hMJ, φ, hφ⟩ :=
    exists_mono_biproduct_lowerStar_of_smul_eq_zero Λ a A hAJ
  have hBJ := fun x (hx : x ∈ Ring.jacobson Λ) ↦
    smul_id_biproduct_lowerStar_constantSheaf π M hMJ hx
  have hBτ := fun q ↦ isIso_tensorBaseChangeHomologyMap'_app_biproduct_lowerStar_constantSheaf Λ p
    h e f' g w 𝓕 π q (fun i ↦ hgood (π i) q) M hMJ
  have := isConstructibleSheaf_biproduct_lowerStar_constantSheaf π M
  have : IsConstructibleSheaf (cokernel φ) := IsConstructibleSheaf.cokernel φ
  let S := ShortComplex.mk φ (cokernel.π φ) (cokernel.condition φ)
  have hS : S.ShortExact := ShortComplex.ShortExact.mk'
    (ShortComplex.exact_of_g_is_cokernel _ (cokernelIsCokernel φ)) inferInstance inferInstance
  refine ⟨_, cokernel φ, φ, cokernel.π φ, cokernel.condition φ, ⟨hBJ, hBτ⟩,
    ⟨inferInstance, fun x hx ↦ smul_id_eq_zero_of_epi (cokernel.π φ) (hBJ x hx)⟩, fun q ↦ ?_⟩
  obtain ⟨h₁, h₂, h₃⟩ := exact_upperStar_tensorRight Λ p
    (tensorBaseChangeHomologySheaf (ModuleCat.{u + 1} Λ) f' g 𝓕 q) S hS hBJ
  obtain ⟨δ, hδ, h₄, h₅⟩ := exists_δ_tensorBaseChangeHomologyTarget _ p h e 𝓕 S
    (shortExact_map_tensorBaseChangeHomologyTargetSheaf Λ p h e 𝓕 S hS hBJ) q
  exact ⟨h₁, h₂, h₃, δ, hδ, h₄, h₅⟩

/-- If the degree-wise base change maps are isomorphisms at the sheaves `π_* Λ / J π_* Λ` for
finite morphisms `π`, they are isomorphisms at every sheaf, on `X` of finite type over a field
and for `h` quasi-compact and quasi-separated. -/
theorem isIso_tensorBaseChangeHomologyMap_app_of_cokernel_lowerStar [QuasiCompact h]
    [QuasiSeparated h] {K : Type u} [Field K]
    (a : X ⟶ Spec (.of K)) [LocallyOfFiniteType a] [QuasiCompact a]
    (h𝓕 : ∀ x ∈ Ring.jacobson Λ, x • 𝟙 𝓕 = 0)
    (hgood : ∀ {Xᵢ : Scheme.{u}} (π : Xᵢ ⟶ X) [IsFinite π] (q : ℤ),
      IsIso ((tensorBaseChangeHomologyMap (ModuleCat.{u + 1} Λ) p h e f' g w 𝓕 q).app
        (cokernel (smulDesc (Ring.jacobson Λ) ((π)_*[ModuleCat.{u + 1} Λ].obj (𝟙_ _))))))
    (q : ℤ) (𝓖 : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    IsIso ((tensorBaseChangeHomologyMap (ModuleCat.{u + 1} Λ) p h e f' g w 𝓕 q).app 𝓖) := by
  have := QuasiCompact.compactSpace_of_compactSpace a
  have : IsNoetherian X := { __ := LocallyOfFiniteType.isLocallyNoetherian a }
  rw [isIso_tensorBaseChangeHomologyMap_app_iff_cokernel_smulDesc Λ p h e f' g w 𝓕 h𝓕,
    ← isIso_tensorBaseChangeHomologyMap'_app_iff]
  let Q := cokernel (smulDesc (Ring.jacobson Λ) 𝓖)
  have hQ : ∀ x ∈ Ring.jacobson Λ, x • 𝟙 Q = 0 := fun x hx ↦ smul_id_cokernel_smulDesc _ _ hx
  obtain ⟨I, _, _, D, c, hc, hD, hmono, ⟨hcol⟩⟩ := exists_isColimit_isConstructibleSheaf Q
  have : PreservesColimitsOfShape I ((p)^*[ModuleCat.{u + 1} Λ] ⋙
      tensorRight (tensorBaseChangeHomologySheaf (ModuleCat.{u + 1} Λ) f' g 𝓕 q)) :=
    inferInstance
  have := preservesColimitsOfShape_singleFunctor_rightDerivedLowerStar Λ h q I
  have : PreservesColimitsOfShape I
      (tensorBaseChangeHomologyTarget (ModuleCat.{u + 1} Λ) p h e 𝓕 q) :=
    comp_preservesColimitsOfShape
      (tensorBaseChangeHomologyTargetSheaf (ModuleCat.{u + 1} Λ) p h e 𝓕)
      (higherDirectImageFunctor (ModuleCat.{u + 1} Λ) h q)
  have key := NatTrans.isIso_app_of_isColimit_of_preservesColimit
    (tensorBaseChangeHomologyMap' (ModuleCat.{u + 1} Λ) p h e f' g w 𝓕 q) hcol fun j ↦ by
      have := hD j
      rw [isIso_tensorBaseChangeHomologyMap'_app_iff]
      exact isIso_tensorBaseChangeHomologyMap_app_of_isConstructibleSheaf Λ p h e f' g w 𝓕 a
        hgood q (D.obj j) fun x hx ↦ by
          have := hmono j
          exact smul_id_eq_zero_of_mono (c.ι.app j) (hc ▸ hQ x hx)
  exact NatTrans.isIso_app_of_isIso_app_of_eq key hc

end ModuleCat

end Etale

end AlgebraicGeometry
