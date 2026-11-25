/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.WeilSheaf.CohomologyExact
public import WeilConjectures.WeilSheaf.GeometricCoinvariants
public import WeilConjectures.WeilSheaf.StalkConstantSheaf
public import WeilConjectures.WeilSheaf.StrictWeilComplex

/-!
# The functor from Weil complexes to strict Weil complexes is not faithful

Blueprint `definition-weil-structure` (complement): the functor
`AlgebraicGeometry.WeilComplex.toStrictWeilComplex`, `K ↦ (For(K), θ_K)`, from Weil complexes to
strict Weil complexes is not faithful. On the point `Spec k₀`, whose geometric fiber is
`Spec k̄`, the Jordan block `J = ℚ̄_ℓ ⊕ ℚ̄_ℓ` with Frobenius `[[1, 1], [0, 1]]` is a nonsplit
extension `0 → ℚ̄_ℓ → J → ℚ̄_ℓ → 0` of Weil sheaves; its class is a nonzero morphism
`δ : ℚ̄_ℓ ⟶ ℚ̄_ℓ[1]` of Weil complexes. Forgetting the Frobenius, the extension splits, so
`For(δ) = 0`.

## The Jordan block

For an algebra `(a, φ : F a ≅ a)` of an additive endofunctor `F`, the Jordan block
`CategoryTheory.Endofunctor.IsoAlgebra.jordanBlock` is `a ⊞ a` with structure isomorphism
`F (a ⊞ a) ≅ F a ⊞ F a --φ ⊞ φ--> a ⊞ a --[[1, 1], [0, 1]]--> a ⊞ a`. The inclusion of the first
summand and the projection to the second one are morphisms of algebras. If an additive functor
`G` with `G ≅ F ⋙ G` (here the global sections) turns `φ` into the identity of a nonzero object,
the projection has no section
(`CategoryTheory.Endofunctor.IsoAlgebra.not_isSplitEpi_jordanBlockSnd`):
on `G (a ⊞ a)` the Frobenius is the unipotent matrix, which has no invariant complement.

For the constant Weil sheaf `ℚ̄_ℓ` on a `k₀`-scheme with connected geometric fiber `X̄`, the
functor is `Γ(X̄, -)`: the Frobenius of `Γ(X̄, ℚ̄_ℓ) = ℚ̄_ℓ` is the identity.

## The class of the extension

The Jordan block extension is short exact; its class is the connecting morphism
`δ : ℚ̄_ℓ[0] ⟶ ℚ̄_ℓ[0][1]` of the distinguished triangle of the derived category of pro-étale Weil
sheaves (`ShortComplex.ShortExact.singleδ`). If `δ = 0`, the projection `J[0] ⟶ ℚ̄_ℓ[0]` is
split, and so is `J ⟶ ℚ̄_ℓ`, the single functor being fully faithful; hence `δ ≠ 0`. Forgetting
the Frobenius gives a distinguished triangle whose first morphism is a split monomorphism, so the
image of `δ` vanishes. No vanishing of `Hom(ℚ̄_ℓ, ℚ̄_ℓ[1])` in the derived category of `ℓ`-adic
sheaves on `Spec k̄` is needed.

## Main results

- `CategoryTheory.Endofunctor.IsoAlgebra.jordanBlock`: the Jordan block.
- `CategoryTheory.Endofunctor.IsoAlgebra.not_isSplitEpi_jordanBlockSnd`: it is nonsplit.
- `AlgebraicGeometry.ProEtaleWeilSheaf.not_isSplitEpi_jordanBlockSnd_adicConstant`: the Jordan
  block of `ℚ̄_ℓ` is nonsplit on a scheme with connected geometric fiber.
- `AlgebraicGeometry.ProEtaleWeilSheaf.jordanδ_ne_zero` and
  `AlgebraicGeometry.ProEtaleWeilSheaf.map_jordanδ`: its class is nonzero, and zero after
  forgetting the Frobenius.
- `AlgebraicGeometry.WeilComplex.exists_ne_zero_forget_map_eq_zero`,
  `AlgebraicGeometry.WeilComplex.not_faithful_toStrictWeilComplex` and
  `AlgebraicGeometry.WeilComplex.not_faithful_toStrictWeilComplex_spec`: the functor from Weil
  complexes to strict Weil complexes is not faithful, in particular on the point `Spec k₀`.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace CategoryTheory.Endofunctor.IsoAlgebra

variable {C : Type*} [Category C] [Preadditive C] [HasBinaryBiproducts C]

/-- The unipotent automorphism `(x, y) ↦ (x + y, y)` of `a ⊞ a`, with matrix `[[1, 1], [0, 1]]`. -/
@[simps]
noncomputable def biprodUnipotent (a : C) : a ⊞ a ≅ a ⊞ a where
  hom := 𝟙 _ + biprod.snd ≫ biprod.inl
  inv := 𝟙 _ - biprod.snd ≫ biprod.inl
  hom_inv_id := by simp
  inv_hom_id := by simp

variable {F : C ⥤ C} [F.Additive]

/-- The Jordan block on an algebra `(a, φ)`: the algebra `a ⊞ a` with structure isomorphism
`F (a ⊞ a) ≅ F a ⊞ F a --φ ⊞ φ--> a ⊞ a --[[1, 1], [0, 1]]--> a ⊞ a`, a self-extension of
`(a, φ)`. -/
noncomputable def jordanBlock (K : IsoAlgebra F) : IsoAlgebra F :=
  haveI : PreservesBinaryBiproducts F := preservesBinaryBiproducts_of_preservesBiproducts F
  mk (K.carrier ⊞ K.carrier)
    (F.mapBiprod K.carrier K.carrier ≪≫ biprod.mapIso K.str K.str ≪≫ biprodUnipotent K.carrier)

lemma jordanBlock_carrier (K : IsoAlgebra F) :
    (jordanBlock K).carrier = (K.carrier ⊞ K.carrier) :=
  rfl

/-- The structure isomorphism of the Jordan block, on the first summand of the target:
`(x, y) ↦ φ x + φ y`. -/
@[reassoc]
lemma jordanBlock_str_hom_fst (K : IsoAlgebra F) :
    (jordanBlock K).str.hom ≫ (biprod.fst : K.carrier ⊞ K.carrier ⟶ K.carrier) =
      F.map (biprod.fst : K.carrier ⊞ K.carrier ⟶ K.carrier) ≫ K.str.hom +
        F.map (biprod.snd : K.carrier ⊞ K.carrier ⟶ K.carrier) ≫ K.str.hom := by
  simp [jordanBlock]

/-- The structure isomorphism of the Jordan block, on the second summand of the target:
`(x, y) ↦ φ y`. -/
@[reassoc]
lemma jordanBlock_str_hom_snd (K : IsoAlgebra F) :
    (jordanBlock K).str.hom ≫ (biprod.snd : K.carrier ⊞ K.carrier ⟶ K.carrier) =
      F.map (biprod.snd : K.carrier ⊞ K.carrier ⟶ K.carrier) ≫ K.str.hom := by
  simp [jordanBlock]

/-- The inclusion of the first summand into the Jordan block, a morphism of algebras. -/
noncomputable def jordanBlockInl (K : IsoAlgebra F) : K ⟶ jordanBlock K :=
  ObjectProperty.homMk
    { f := (biprod.inl : K.carrier ⟶ K.carrier ⊞ K.carrier)
      h := by
        refine biprod.hom_ext _ _ ?_ ?_
        · rw [Category.assoc, ← str_hom, jordanBlock_str_hom_fst, Preadditive.comp_add,
            ← F.map_comp_assoc, ← F.map_comp_assoc]
          simp
        · rw [Category.assoc, ← str_hom, jordanBlock_str_hom_snd, ← F.map_comp_assoc]
          simp }

/-- The projection of the Jordan block to the second summand, a morphism of algebras. -/
noncomputable def jordanBlockSnd (K : IsoAlgebra F) : jordanBlock K ⟶ K :=
  ObjectProperty.homMk
    { f := (biprod.snd : K.carrier ⊞ K.carrier ⟶ K.carrier)
      h := by
        rw [← str_hom, ← str_hom, jordanBlock_str_hom_snd] }

@[simp]
lemma jordanBlockInl_hom_f (K : IsoAlgebra F) :
    (jordanBlockInl K).hom.f = (biprod.inl : K.carrier ⟶ K.carrier ⊞ K.carrier) :=
  rfl

@[simp]
lemma jordanBlockSnd_hom_f (K : IsoAlgebra F) :
    (jordanBlockSnd K).hom.f = (biprod.snd : K.carrier ⊞ K.carrier ⟶ K.carrier) :=
  rfl

@[reassoc (attr := simp)]
lemma jordanBlockInl_jordanBlockSnd (K : IsoAlgebra F) :
    jordanBlockInl K ≫ jordanBlockSnd K = 0 :=
  ObjectProperty.hom_ext _ (Algebra.Hom.ext (biprod.inl_snd (X := K.carrier) (Y := K.carrier)))

/-- **The Jordan block is nonsplit.** Let `G : C ⥤ D` be an additive functor with an isomorphism
`γ : G ≅ F ⋙ G` turning the structure isomorphism of `K` into the identity of `G K`, a nonzero
object. Then the projection `jordanBlock K ⟶ K` has no section: on `G (K ⊞ K)` the transported
structure is the unipotent matrix `[[1, 1], [0, 1]]`, and a section `σ` invariant under it would
satisfy `σ ≫ G fst = σ ≫ G fst + 𝟙`. -/
lemma not_isSplitEpi_jordanBlockSnd {D : Type*} [Category D] [Preadditive D] (G : C ⥤ D)
    [G.Additive] (γ : G ≅ F ⋙ G) (K : IsoAlgebra F)
    (hK : γ.hom.app K.carrier ≫ G.map K.str.hom = 𝟙 _) (hK' : ¬ IsZero (G.obj K.carrier)) :
    ¬ IsSplitEpi (jordanBlockSnd K) := by
  rintro ⟨⟨s, hs⟩⟩
  have hs' : G.map s.hom.f ≫ G.map (biprod.snd : K.carrier ⊞ K.carrier ⟶ K.carrier) = 𝟙 _ := by
    rw [← G.map_comp, ← jordanBlockSnd_hom_f, ← comp_hom_f, hs, id_hom_f, G.map_id]
  have h₁ : G.map s.hom.f ≫ γ.hom.app (jordanBlock K).carrier ≫
      G.map (jordanBlock K).str.hom = G.map s.hom.f := by
    have hn := γ.hom.naturality s.hom.f
    rw [Functor.comp_map] at hn
    rw [reassoc_of% hn, ← G.map_comp, str_hom, s.hom.h, G.map_comp, ← str_hom,
      reassoc_of% hK]
  have hf (f : K.carrier ⊞ K.carrier ⟶ K.carrier) :
      γ.hom.app (jordanBlock K).carrier ≫ G.map (F.map f) = G.map f ≫ γ.hom.app K.carrier :=
    (γ.hom.naturality f).symm
  have h₂ : G.map s.hom.f ≫ G.map (biprod.fst : K.carrier ⊞ K.carrier ⟶ K.carrier) =
      G.map s.hom.f ≫ G.map (biprod.fst : K.carrier ⊞ K.carrier ⟶ K.carrier) + 𝟙 _ := by
    conv_lhs => rw [← h₁]
    rw [Category.assoc, Category.assoc, ← G.map_comp, jordanBlock_str_hom_fst, G.map_add,
      G.map_comp, G.map_comp, Preadditive.comp_add, Preadditive.comp_add, reassoc_of% hf,
      reassoc_of% hf, hK, reassoc_of% hs', Category.comp_id]
  exact hK' ((IsZero.iff_id_eq_zero _).2 (by simpa using h₂))

end CategoryTheory.Endofunctor.IsoAlgebra

namespace AlgebraicGeometry

open Endofunctor ProEtale Pretriangulated

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime]
  {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]

namespace ProEtaleWeilSheaf

variable (k₀ l X) in
/-- The global sections `Γ(X̄, -)` of `ℓ`-adic pro-étale sheaves on the geometric fiber. -/
noncomputable abbrev adicGlobalSections :
    AdicSheaf l (X ↘ Spec (CommRingCat.of k₀)).geometricFiber ⥤ WeilCoefficients.{u} l :=
  AdicSheaf.forget _ ⋙ Sheaf.Γ _ _

variable (k₀ l X) in
/-- The invariance `Γ(X̄, M) ≅ Γ(X̄, Fr_X^* M)` of global sections under the Frobenius pullback
`Fr_X^* = (Fr_X⁻¹)_*`, natural in `M`. -/
noncomputable def adicGlobalSectionsFrobeniusIso :
    adicGlobalSections k₀ l X ≅
      WeilSheaf.frobeniusPullback k₀ l X ⋙ adicGlobalSections k₀ l X :=
  NatIso.ofComponents
    (fun M ↦ ((globalSectionsLowerStarIso _
      (X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.asIso.inv).app M.X).symm)
    (fun f ↦ (globalSectionsLowerStarIso _
      (X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.asIso.inv).inv.naturality f.hom)

section Connected

variable [Fact (ringChar k₀ ≠ l)] [ConnectedSpace (X ↘ Spec (CommRingCat.of k₀)).geometricFiber]

/-- On a scheme with connected geometric fiber, the Frobenius of the global sections
`Γ(X̄, ℚ̄_ℓ) = ℚ̄_ℓ` of the constant Weil sheaf is the identity: it fixes the unit section, which
spans the line `Γ(X̄, ℚ̄_ℓ)`. -/
lemma adicGlobalSectionsFrobeniusIso_hom_app_comp_adicConstant_str :
    (adicGlobalSectionsFrobeniusIso k₀ l X).hom.app (adicConstant k₀ l X).carrier ≫
      (adicGlobalSections k₀ l X).map (adicConstant k₀ l X).str.hom = 𝟙 _ :=
  WeilCoefficients.eq_id_of_finrank_eq_one _ (finrank_globalSections_adicConstantSheaf _)
    (oneGlobalSection _) (oneGlobalSection_ne_zero _) WeilSheaf.adicConstant_globalSections_str_one

omit [Fact (ringChar k₀ ≠ l)] in
/-- The global sections `Γ(X̄, ℚ̄_ℓ)` of the constant sheaf on a connected `X̄` are nonzero. -/
lemma not_isZero_adicGlobalSections_adicConstant :
    ¬ IsZero ((adicGlobalSections k₀ l X).obj (adicConstant k₀ l X).carrier) := fun h ↦
  oneGlobalSection_ne_zero (l := l) (X ↘ Spec (CommRingCat.of k₀)).geometricFiber
    (by simpa using congrArg (fun φ ↦ φ.hom (oneGlobalSection (l := l) _)) (h.eq_of_src (𝟙 _) 0))

/-- **The Jordan block of `ℚ̄_ℓ` is nonsplit**: on a scheme with connected geometric fiber, the
extension `0 → ℚ̄_ℓ → J → ℚ̄_ℓ → 0` of pro-étale Weil sheaves with Frobenius `[[1, 1], [0, 1]]`
on `J = ℚ̄_ℓ ⊕ ℚ̄_ℓ` has no splitting. -/
theorem not_isSplitEpi_jordanBlockSnd_adicConstant :
    ¬ IsSplitEpi (IsoAlgebra.jordanBlockSnd (adicConstant k₀ l X)) := by
  have : (adicGlobalSections k₀ l X).Additive := by
    have : (Sheaf.Γ (Scheme.ProEt.topology (X ↘ Spec (CommRingCat.of k₀)).geometricFiber)
        (WeilCoefficients.{u} l)).Additive := Functor.additive_of_preserves_binary_products _
    infer_instance
  exact IsoAlgebra.not_isSplitEpi_jordanBlockSnd _ (adicGlobalSectionsFrobeniusIso k₀ l X) _
    adicGlobalSectionsFrobeniusIso_hom_app_comp_adicConstant_str
    not_isZero_adicGlobalSections_adicConstant

end Connected

variable (K : ProEtaleWeilSheaf k₀ l X)

/-- The Jordan block extension `0 → K → J → K → 0` of a pro-étale Weil sheaf. -/
noncomputable abbrev jordanShortComplex : ShortComplex (ProEtaleWeilSheaf k₀ l X) :=
  ShortComplex.mk (IsoAlgebra.jordanBlockInl K) (IsoAlgebra.jordanBlockSnd K)
    (IsoAlgebra.jordanBlockInl_jordanBlockSnd K)

/-- The Jordan block extension is short exact: forgetting the Frobenius, it is the split short
exact sequence `0 → K → K ⊞ K → K → 0`, and the forgetful functor is faithful and exact. -/
lemma shortExact_jordanShortComplex : (jordanShortComplex K).ShortExact := by
  have hs : ((jordanShortComplex K).map (IsoAlgebra.forget _)).ShortExact :=
    ShortComplex.Splitting.shortExact
      { r := (biprod.fst : K.carrier ⊞ K.carrier ⟶ K.carrier)
        s := (biprod.inr : K.carrier ⟶ K.carrier ⊞ K.carrier)
        f_r := biprod.inl_fst
        s_g := biprod.inr_snd
        id := biprod.total }
  have := hs.mono_f
  have := hs.epi_g
  exact ShortComplex.ShortExact.mk'
    (((jordanShortComplex K).exact_map_iff_of_faithful (IsoAlgebra.forget _)).1 hs.exact)
    ((IsoAlgebra.forget _).mono_of_mono_map ‹_›) ((IsoAlgebra.forget _).epi_of_epi_map ‹_›)

/-- The class `δ : K[0] ⟶ K[0][1]` of the Jordan block extension in the derived category of
pro-étale Weil sheaves. -/
noncomputable abbrev jordanδ :
    (DerivedCategory.singleFunctor _ 0).obj K ⟶
      ((DerivedCategory.singleFunctor _ 0).obj K)⟦(1 : ℤ)⟧ :=
  (shortExact_jordanShortComplex K).singleδ

/-- If the Jordan block extension is nonsplit, its class `δ` is nonzero: if `δ = 0`, the
projection `J[0] ⟶ K[0]` is an epimorphism in the triangulated derived category, hence split, and
a section comes from a section of `J ⟶ K`, the single functor being fully faithful. -/
lemma jordanδ_ne_zero (hK : ¬ IsSplitEpi (IsoAlgebra.jordanBlockSnd K)) : jordanδ K ≠ 0 := by
  intro h
  have hT := (shortExact_jordanShortComplex K).singleTriangle_distinguished
  have : Epi ((DerivedCategory.singleFunctor _ 0).map (IsoAlgebra.jordanBlockSnd K)) :=
    Triangle.epi₂ _ hT h
  have := isSplitEpi_of_epi ((DerivedCategory.singleFunctor _ 0).map
    (IsoAlgebra.jordanBlockSnd K))
  exact hK ⟨⟨(DerivedCategory.singleFunctor _ 0).preimage
    (section_ ((DerivedCategory.singleFunctor _ 0).map (IsoAlgebra.jordanBlockSnd K))),
    (DerivedCategory.singleFunctor _ 0).map_injective (by simp)⟩⟩

/-- Forgetting the Frobenius kills the class of the Jordan block extension: the image of the
triangle `K[0] → J[0] → K[0] → K[0][1]` is distinguished with split monomorphic first morphism,
the underlying extension `0 → K → K ⊞ K → K → 0` being split. -/
lemma map_jordanδ : (IsoAlgebra.forget _).mapDerivedCategory.map (jordanδ K) = 0 := by
  have hT := Functor.map_distinguished
    (IsoAlgebra.forget (WeilSheaf.frobeniusPullback k₀ l X)).mapDerivedCategory _
    (shortExact_jordanShortComplex K).singleTriangle_distinguished
  let e :=
    (IsoAlgebra.forget (WeilSheaf.frobeniusPullback k₀ l X)).mapDerivedCategorySingleFunctor 0
  have hmono : Mono ((IsoAlgebra.forget _).mapDerivedCategory.map
      ((DerivedCategory.singleFunctor _ 0).map (IsoAlgebra.jordanBlockInl K))) := by
    refine SplitMono.mono ⟨e.hom.app (IsoAlgebra.jordanBlock K) ≫
      (DerivedCategory.singleFunctor _ 0).map
        (biprod.fst : K.carrier ⊞ K.carrier ⟶ K.carrier) ≫ e.inv.app K, ?_⟩
    have hn := e.hom.naturality (IsoAlgebra.jordanBlockInl K)
    simp only [Functor.comp_map] at hn
    rw [reassoc_of% hn]
    simp [← Functor.map_comp_assoc]
  exact (Preadditive.IsIso.comp_right_eq_zero _ _).1 (Triangle.mor₃_eq_zero_of_mono₁ _ hT hmono)

end ProEtaleWeilSheaf

namespace WeilComplex

variable [Fact (ringChar k₀ ≠ l)]

variable (k₀ l X) in
/-- On a `k₀`-scheme with connected geometric fiber, the class `δ : ℚ̄_ℓ ⟶ ℚ̄_ℓ[1]` of the Jordan
block extension is a nonzero morphism of Weil complexes whose underlying morphism of complexes of
`ℓ`-adic sheaves is zero. -/
theorem exists_ne_zero_forget_map_eq_zero
    [ConnectedSpace (X ↘ Spec (CommRingCat.of k₀)).geometricFiber] :
    ∃ (K L : WeilComplex k₀ l X) (f : K ⟶ L), f ≠ 0 ∧ forget.map f = 0 := by
  refine ⟨WeilSheaf.toComplex.obj (WeilSheaf.adicConstant k₀ l X),
    ⟨((DerivedCategory.singleFunctor _ 0).obj (WeilSheaf.adicConstant k₀ l X).obj)⟦(1 : ℤ)⟧,
      (WeilComplex.objectProperty k₀ l X).le_shift 1 _
        (WeilSheaf.toComplex.obj (WeilSheaf.adicConstant k₀ l X)).property⟩,
    ObjectProperty.homMk (ProEtaleWeilSheaf.jordanδ (ProEtaleWeilSheaf.adicConstant k₀ l X)),
    fun h ↦ ProEtaleWeilSheaf.jordanδ_ne_zero _
      ProEtaleWeilSheaf.not_isSplitEpi_jordanBlockSnd_adicConstant (congrArg (·.hom) h),
    ProEtaleWeilSheaf.map_jordanδ _⟩

/-- Blueprint `definition-weil-structure` (complement): on a `k₀`-scheme with connected geometric
fiber, the functor `K ↦ (For(K), θ_K)` from Weil complexes to strict Weil complexes is not
faithful: the class of the nonsplit Jordan block extension of `ℚ̄_ℓ` by `ℚ̄_ℓ` is a nonzero
morphism `ℚ̄_ℓ ⟶ ℚ̄_ℓ[1]` of Weil complexes, which becomes zero after forgetting the Weil
structure. -/
theorem not_faithful_toStrictWeilComplex
    [ConnectedSpace (X ↘ Spec (CommRingCat.of k₀)).geometricFiber] :
    ¬ (toStrictWeilComplex (k₀ := k₀) (l := l) (X := X)).Faithful := by
  intro _
  obtain ⟨K, L, f, hf, hf₀⟩ := exists_ne_zero_forget_map_eq_zero k₀ l X
  refine hf (toStrictWeilComplex.map_injective (ObjectProperty.hom_ext _ (Algebra.Hom.ext ?_)))
  rw [toStrictWeilComplex_map_hom_f, toStrictWeilComplex_map_hom_f, hf₀]
  exact (Functor.map_zero (IsoAlgebra.forget _).mapDerivedCategory _ _).symm

/-- The geometric fiber `Spec k̄` of the point `Spec k₀` is connected. -/
instance : ConnectedSpace
    (Spec (CommRingCat.of k₀) ↘ Spec (CommRingCat.of k₀)).geometricFiber :=
  have : ConnectedSpace (Spec (.of (AlgebraicClosure k₀))) :=
    inferInstanceAs (ConnectedSpace (Spec (CommRingCat.of (AlgebraicClosure k₀))))
  (WeilSheaf.geometricFiberSpecIso k₀).hom.homeomorph.connectedSpace_iff.1 this

/-- Blueprint `definition-weil-structure` (complement): on the point `Spec k₀`, whose geometric
fiber is `Spec k̄`, the functor from Weil complexes to strict Weil complexes is not faithful. -/
theorem not_faithful_toStrictWeilComplex_spec :
    ¬ (toStrictWeilComplex (k₀ := k₀) (l := l) (X := Spec (CommRingCat.of k₀))).Faithful :=
  not_faithful_toStrictWeilComplex

end WeilComplex

end AlgebraicGeometry
