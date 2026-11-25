/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.WeilSheaf.FourierInversion.Defs
public import WeilConjectures.WeilSheaf.SplitTorsor

/-!
# The Artin–Schreier covering of the affine plane

Let `k₀` be a finite field with `q` elements. The Artin–Schreier map `AS : 𝔸² ⟶ 𝔸²`,
`x ↦ x^q - x` coordinatewise, is a finite étale torsor under `k₀²` acting by translations
(`AlgebraicGeometry.isTorsorSplit_planeArtinSchreierMap`). The linear forms
`x ↦ c₁ x₁ + c₂ x₂` with coefficients in `k₀` intertwine it with the Artin–Schreier map of the
affine line (`AlgebraicGeometry.affineLine.linearForm_comp_artinSchreierMap`).

For a `k₀`-scheme `X` with two global functions `f₁, f₂`, the pullback of `AS` along
`(f₁, f₂) : X ⟶ 𝔸²` is a finite étale `k₀²`-torsor `π : X' ⟶ X`
(`AlgebraicGeometry.artinSchreierPlaneCover`), on which all the Artin–Schreier sheaves
`ℒ_ψ(c₁ f₁ + c₂ f₂)` become trivial.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

variable (k₀ : Type u) [Field k₀] [Finite k₀]

local notation "S₀" => Spec (CommRingCat.of k₀)

local notation "φ₀" => CommRingCat.Hom.hom (Iso.inv (Scheme.ΓSpecIso (CommRingCat.of k₀)))


section AffineSpace

/-- Over a finite field `k` with `q` elements, every geometric point of `𝔸(n; k)` lifts along the
Artin–Schreier map `AS_q`: the equations `T ^ q - T = c` have roots in an algebraically closed
field. -/
lemma AffineSpace.exists_comp_artinSchreierMap_eq_of_isAlgClosed (n : Type u) (k : Type u)
    [Field k] [Fintype k] {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (y : Spec (.of Ω) ⟶ 𝔸(n; Spec (.of k))) :
    ∃ t : Spec (.of Ω) ⟶ 𝔸(n; Spec (.of k)),
      t ≫ AffineSpace.artinSchreierMap n (Spec (.of k)) (Fintype.card k) = y := by
  have key (c : Ω) : ∃ d : Ω, d ^ Fintype.card k - d = c := by
    have hlt : (Polynomial.X : Polynomial Ω).degree <
        ((Polynomial.X : Polynomial Ω) ^ Fintype.card k).degree := by
      rw [Polynomial.degree_X, Polynomial.degree_X_pow]
      exact_mod_cast Fintype.one_lt_card
    obtain ⟨d, hd⟩ := IsAlgClosed.exists_root (Polynomial.X ^ Fintype.card k - Polynomial.X -
      Polynomial.C c) (by
        rw [Polynomial.degree_sub_C (by
          rw [Polynomial.degree_sub_eq_left_of_degree_lt hlt, Polynomial.degree_X_pow]
          exact_mod_cast Fintype.card_pos)]
        rw [Polynomial.degree_sub_eq_left_of_degree_lt hlt, Polynomial.degree_X_pow]
        exact_mod_cast Fintype.card_ne_zero)
    simp only [Polynomial.IsRoot, Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X,
      Polynomial.eval_C] at hd
    exact ⟨d, sub_eq_zero.mp hd⟩
  choose d hd using fun i : n ↦
    key ((Scheme.ΓSpecIso (.of Ω)).hom.hom (y.appTop (AffineSpace.coord (Spec (.of k)) i)))
  refine ⟨AffineSpace.homOfVector (y ≫ 𝔸(n; Spec (.of k)) ↘ Spec (.of k))
    fun i ↦ (Scheme.ΓSpecIso (.of Ω)).inv.hom (d i), AffineSpace.hom_ext ?_ fun i ↦ ?_⟩
  · rw [Category.assoc, AffineSpace.artinSchreierMap_over, AffineSpace.homOfVector_over]
  · rw [Scheme.Hom.comp_appTop, CommRingCat.comp_apply, AffineSpace.artinSchreierMap_appTop_coord,
      map_sub, map_pow, AffineSpace.homOfVector_appTop_coord, ← map_pow, ← map_sub, hd i]
    exact (Scheme.ΓSpecIso (.of Ω)).hom_inv_id_apply _

/-- Over a finite field `k` with `q` elements, the Artin–Schreier map `AS_q` of `𝔸(n; k)` is
surjective: every point has a geometric point over it, which lifts along `AS_q`. -/
lemma AffineSpace.surjective_artinSchreierMap_of_finiteField (n : Type u) (k : Type u) [Field k]
    [Fintype k] :
    Function.Surjective (AffineSpace.artinSchreierMap n (Spec (.of k)) (Fintype.card k)).base := by
  intro x
  obtain ⟨t, ht⟩ := AffineSpace.exists_comp_artinSchreierMap_eq_of_isAlgClosed n k
    (Spec.map (CommRingCat.ofHom (algebraMap (𝔸(n; Spec (.of k)).residueField x)
      (AlgebraicClosure (𝔸(n; Spec (.of k)).residueField x)))) ≫
      𝔸(n; Spec (.of k)).fromSpecResidueField x)
  obtain ⟨p⟩ : Nonempty (Spec (.of (AlgebraicClosure (𝔸(n; Spec (.of k)).residueField x)))) :=
    inferInstance
  refine ⟨t.base p, ?_⟩
  rw [← Scheme.Hom.comp_apply, ht, Scheme.Hom.comp_apply]
  exact Scheme.fromSpecResidueField_apply _ _

end AffineSpace

section Plane

/-- The index type `{0, 1}` of the coordinates of the affine plane `𝔸(planeIndex; k₀)`. -/
abbrev planeIndex : Type u := ULift.{u} (Fin 2)

/-- The Artin–Schreier map `AS : x ↦ x^q - x` of the affine plane over `k₀`, `q = #k₀`, applied
coordinatewise. -/
noncomputable def planeArtinSchreierMap : 𝔸(planeIndex; S₀) ⟶ 𝔸(planeIndex; S₀) :=
  letI := Fintype.ofFinite k₀
  AffineSpace.artinSchreierMap planeIndex S₀ (Fintype.card k₀)

instance : (planeArtinSchreierMap k₀).IsOver S₀ :=
  ⟨AffineSpace.artinSchreierMap_over _ _ _⟩

instance : IsFinite (planeArtinSchreierMap k₀) := by
  let := Fintype.ofFinite k₀
  exact AffineSpace.isFinite_artinSchreierMap _ _ Fintype.one_lt_card.ne'

instance : Etale (planeArtinSchreierMap k₀) := by
  let := Fintype.ofFinite k₀
  exact AffineSpace.etale_artinSchreierMap _ _ (by
    rw [← map_natCast (Scheme.ΓSpecIso (.of k₀)).inv.hom, FiniteField.cast_card_eq_zero,
      map_zero])

instance : Surjective (planeArtinSchreierMap k₀) := by
  let := Fintype.ofFinite k₀
  exact ⟨AffineSpace.surjective_artinSchreierMap_of_finiteField _ k₀⟩

/-- A morphism `g : Y ⟶ Z` over `T` fixes the pullbacks of global functions on `T`. -/
private lemma appTop_appTop_of_comp_eq {Y Z T : Scheme.{u}} (g : Y ⟶ Z) (p : Z ⟶ T)
    (p' : Y ⟶ T) (h : g ≫ p = p') (s : Γ(T, ⊤)) : g.appTop (p.appTop s) = p'.appTop s := by
  rw [← h, Scheme.Hom.comp_appTop]
  rfl

/-- The linear form `x ↦ ∑ᵢ cᵢ xᵢ : 𝔸² ⟶ 𝔸¹` over `k₀` with coefficients `c ∈ k₀²`. -/
noncomputable def affineLine.linearForm (c : planeIndex → k₀) :
    𝔸(planeIndex; S₀) ⟶ affineLine k₀ :=
  AffineSpace.homOfVector (𝔸(planeIndex; S₀) ↘ S₀) fun _ ↦
    ∑ i, (𝔸(planeIndex; S₀) ↘ S₀).appTop (φ₀ (c i)) * AffineSpace.coord S₀ i

instance (c : planeIndex → k₀) : (affineLine.linearForm k₀ c).IsOver S₀ :=
  ⟨AffineSpace.homOfVector_over _ _⟩

omit [Finite k₀] in
@[simp]
lemma affineLine.linearForm_appTop_coord (c : planeIndex → k₀) (j : PUnit.{u + 1}) :
    (affineLine.linearForm k₀ c).appTop (AffineSpace.coord S₀ j) =
      ∑ i, (𝔸(planeIndex; S₀) ↘ S₀).appTop (φ₀ (c i)) * AffineSpace.coord S₀ i :=
  AffineSpace.homOfVector_appTop_coord _ _ _

/-- The linear forms with coefficients in `k₀` intertwine the Artin–Schreier maps of the plane
and of the line: `(∑ᵢ cᵢ xᵢ)^q - ∑ᵢ cᵢ xᵢ = ∑ᵢ cᵢ (xᵢ^q - xᵢ)` since `cᵢ^q = cᵢ`. -/
@[reassoc]
lemma affineLine.linearForm_comp_artinSchreierMap (c : planeIndex → k₀) :
    affineLine.linearForm k₀ c ≫ affineLine.artinSchreierMap k₀ =
      planeArtinSchreierMap k₀ ≫ affineLine.linearForm k₀ c := by
  let := Fintype.ofFinite k₀
  refine AffineSpace.hom_ext ?_ fun j ↦ ?_
  · simp only [affineLine.artinSchreierMap, planeArtinSchreierMap, Category.assoc,
      AffineSpace.artinSchreierMap_over, affineLine.linearForm, AffineSpace.homOfVector_over]
  obtain ⟨m, hp, hm⟩ := FiniteField.card k₀ (ringChar k₀)
  have := Fact.mk hp
  nontriviality Γ(𝔸(planeIndex; S₀), ⊤)
  have := CharP.of_ringHom_of_prime ((𝔸(planeIndex; S₀) ↘ S₀).appTop.hom.comp φ₀) hp
    ringChar.Nat.cast_ringChar
  have hc (i : planeIndex) : (𝔸(planeIndex; S₀) ↘ S₀).appTop (φ₀ (c i)) ^ Fintype.card k₀ =
      (𝔸(planeIndex; S₀) ↘ S₀).appTop (φ₀ (c i)) := by
    rw [← map_pow, ← map_pow, FiniteField.pow_card]
  have hAS (i : planeIndex) : (planeArtinSchreierMap k₀).appTop
      ((𝔸(planeIndex; S₀) ↘ S₀).appTop (φ₀ (c i))) =
      (𝔸(planeIndex; S₀) ↘ S₀).appTop (φ₀ (c i)) :=
    appTop_appTop_of_comp_eq _ _ _ (AffineSpace.artinSchreierMap_over _ _ _) _
  rw [Scheme.Hom.comp_appTop, CommRingCat.comp_apply, Scheme.Hom.comp_appTop,
    CommRingCat.comp_apply, affineLine.artinSchreierMap, AffineSpace.artinSchreierMap_appTop_coord,
    map_sub, map_pow, affineLine.linearForm_appTop_coord, map_sum]
  simp only [map_mul, hAS]
  rw [planeArtinSchreierMap]
  simp only [AffineSpace.artinSchreierMap_appTop_coord]
  rw [hm, sum_pow_char_pow, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [mul_pow, ← hm, hc, mul_sub]

/-- The translation `x ↦ x + a` of the affine plane over `k₀` by `a ∈ k₀²`. -/
noncomputable def planeTranslation (a : planeIndex → k₀) :
    𝔸(planeIndex; S₀) ≅ 𝔸(planeIndex; S₀) where
  hom := AffineSpace.translation fun i ↦ φ₀ (a i)
  inv := AffineSpace.translation fun i ↦ φ₀ (-a i)
  hom_inv_id := by
    rw [← AffineSpace.translation_add, ← AffineSpace.translation_zero]
    congr 1
    ext i
    simp
  inv_hom_id := by
    rw [← AffineSpace.translation_add, ← AffineSpace.translation_zero]
    congr 1
    ext i
    simp

instance (a : planeIndex → k₀) : (planeTranslation k₀ a).hom.IsOver S₀ :=
  ⟨AffineSpace.translation_over _⟩

omit [Finite k₀] in
/-- Translation by `a + b` is translation by `a` followed by translation by `b`. -/
lemma planeTranslation_add (a b : planeIndex → k₀) :
    (planeTranslation k₀ (a + b)).hom =
      (planeTranslation k₀ a).hom ≫ (planeTranslation k₀ b).hom := by
  change AffineSpace.translation _ = AffineSpace.translation _ ≫ AffineSpace.translation _
  rw [← AffineSpace.translation_add]
  congr 1
  ext i
  simp

/-- The translations by `k₀²` leave the Artin–Schreier map of the plane invariant. -/
@[reassoc (attr := simp)]
lemma planeTranslation_comp_artinSchreierMap (a : planeIndex → k₀) :
    (planeTranslation k₀ a).hom ≫ planeArtinSchreierMap k₀ = planeArtinSchreierMap k₀ := by
  let := Fintype.ofFinite k₀
  exact AffineSpace.translation_comp_artinSchreierMap_of_finiteField k₀ _ a

/-- The inverse translations leave the Artin–Schreier map of the plane invariant. -/
@[reassoc (attr := simp)]
lemma planeTranslation_inv_comp_artinSchreierMap (a : planeIndex → k₀) :
    (planeTranslation k₀ a).inv ≫ planeArtinSchreierMap k₀ = planeArtinSchreierMap k₀ := by
  rw [Iso.inv_comp_eq, planeTranslation_comp_artinSchreierMap]

omit [Finite k₀] in
/-- A linear form transforms translation by `a` into translation by `∑ᵢ cᵢ aᵢ`. -/
@[reassoc]
lemma planeTranslation_comp_linearForm (a c : planeIndex → k₀) :
    (planeTranslation k₀ a).hom ≫ affineLine.linearForm k₀ c =
      affineLine.linearForm k₀ c ≫ affineLine.translation k₀ (∑ i, c i * a i) := by
  refine AffineSpace.hom_ext ?_ fun j ↦ ?_
  · simp only [planeTranslation, affineLine.translation, affineLine.linearForm, Category.assoc,
      AffineSpace.homOfVector_over, AffineSpace.translation_over]
  have hT (i : planeIndex) : (planeTranslation k₀ a).hom.appTop
      ((𝔸(planeIndex; S₀) ↘ S₀).appTop (φ₀ (c i))) =
      (𝔸(planeIndex; S₀) ↘ S₀).appTop (φ₀ (c i)) :=
    appTop_appTop_of_comp_eq _ _ _ (AffineSpace.translation_over _) _
  have hL : (affineLine.linearForm k₀ c).appTop
      ((affineLine k₀ ↘ S₀).appTop (φ₀ (∑ i, c i * a i))) =
      (𝔸(planeIndex; S₀) ↘ S₀).appTop (φ₀ (∑ i, c i * a i)) :=
    appTop_appTop_of_comp_eq _ _ _ (AffineSpace.homOfVector_over _ _) _
  rw [Scheme.Hom.comp_appTop, CommRingCat.comp_apply, Scheme.Hom.comp_appTop,
    CommRingCat.comp_apply, affineLine.linearForm_appTop_coord, affineLine.translation,
    AffineSpace.translation_appTop_coord, map_add, hL, affineLine.linearForm_appTop_coord,
    map_sum]
  simp only [map_mul, hT]
  simp only [planeTranslation, AffineSpace.translation_appTop_coord, map_sum, map_mul, mul_add,
    Finset.sum_add_distrib]

/-- The Artin–Schreier map of the affine plane over `k₀` is a `k₀²`-torsor: the map
`∐_{a ∈ k₀²} 𝔸² ⟶ 𝔸² ×_{AS} 𝔸²`, `(𝟙, x ↦ x + a)` on the summand indexed by `a`, is an
isomorphism (`AlgebraicGeometry.AffineSpace.isIso_artinSchreierTorsorMap`). -/
lemma isTorsorSplit_planeArtinSchreierMap :
    ProEtale.IsTorsorSplit (planeArtinSchreierMap k₀) (planeTranslation k₀)
      (planeTranslation_comp_artinSchreierMap k₀) := by
  let := Fintype.ofFinite k₀
  exact AffineSpace.isIso_artinSchreierTorsorMap (n := planeIndex) (S := S₀) k₀ φ₀

end Plane

section Cover

variable {k₀}

variable {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]

variable (k₀) in
/-- The morphism `X ⟶ 𝔸²` over `k₀` defined by two global functions `f₁, f₂` on `X`. -/
noncomputable def planeSection (f : planeIndex → Γ(X, ⊤)) : X ⟶ 𝔸(planeIndex; S₀) :=
  AffineSpace.homOfVector (X ↘ S₀) f

instance (f : planeIndex → Γ(X, ⊤)) : (planeSection k₀ f).IsOver S₀ :=
  ⟨AffineSpace.homOfVector_over _ _⟩

omit [Finite k₀] in
/-- Composing `(f₁, f₂) : X ⟶ 𝔸²` with the linear form `∑ᵢ cᵢ xᵢ` gives the function
`∑ᵢ cᵢ fᵢ`. -/
lemma planeSection_comp_linearForm (f : planeIndex → Γ(X, ⊤)) (c : planeIndex → k₀) :
    planeSection k₀ f ≫ affineLine.linearForm k₀ c =
      affineLine.homOfSection k₀ (∑ i, (X ↘ S₀).appTop (φ₀ (c i)) * f i) := by
  refine AffineSpace.hom_ext ?_ fun j ↦ ?_
  · simp only [planeSection, affineLine.homOfSection, affineLine.linearForm, Category.assoc,
      AffineSpace.homOfVector_over]
  have hP (i : planeIndex) : (planeSection k₀ f).appTop
      ((𝔸(planeIndex; S₀) ↘ S₀).appTop (φ₀ (c i))) = (X ↘ S₀).appTop (φ₀ (c i)) :=
    appTop_appTop_of_comp_eq _ _ _ (AffineSpace.homOfVector_over _ _) _
  rw [Scheme.Hom.comp_appTop, CommRingCat.comp_apply, affineLine.linearForm_appTop_coord,
    affineLine.homOfSection, AffineSpace.homOfVector_appTop_coord, map_sum]
  simp only [map_mul, hP]
  simp only [planeSection, AffineSpace.homOfVector_appTop_coord]

variable (k₀) in
/-- The Artin–Schreier covering of `X` defined by two global functions `f₁, f₂`: the pullback
of the Artin–Schreier map of the plane along `(f₁, f₂) : X ⟶ 𝔸²`. -/
noncomputable def artinSchreierPlaneCover (f : planeIndex → Γ(X, ⊤)) : Scheme.{u} :=
  pullback (planeSection k₀ f) (planeArtinSchreierMap k₀)

noncomputable instance (f : planeIndex → Γ(X, ⊤)) :
    (artinSchreierPlaneCover k₀ f).Over S₀ :=
  ⟨pullback.fst _ _ ≫ X ↘ S₀⟩

/-- The covering map `π : X' ⟶ X` of the Artin–Schreier covering. -/
noncomputable def artinSchreierPlaneCover.π (f : planeIndex → Γ(X, ⊤)) :
    artinSchreierPlaneCover k₀ f ⟶ X :=
  pullback.fst _ _

/-- The coordinates `X' ⟶ 𝔸²` of the Artin–Schreier covering, `t` with `t^q - t = f`. -/
noncomputable def artinSchreierPlaneCover.coord (f : planeIndex → Γ(X, ⊤)) :
    artinSchreierPlaneCover k₀ f ⟶ 𝔸(planeIndex; S₀) :=
  pullback.snd _ _

instance (f : planeIndex → Γ(X, ⊤)) : (artinSchreierPlaneCover.π (k₀ := k₀) f).IsOver S₀ :=
  ⟨rfl⟩

/-- The defining equation `t^q - t = f` of the Artin–Schreier covering. -/
@[reassoc]
lemma artinSchreierPlaneCover.condition (f : planeIndex → Γ(X, ⊤)) :
    artinSchreierPlaneCover.coord f ≫ planeArtinSchreierMap k₀ =
      artinSchreierPlaneCover.π f ≫ planeSection k₀ f :=
  pullback.condition.symm

instance (f : planeIndex → Γ(X, ⊤)) :
    (artinSchreierPlaneCover.coord (k₀ := k₀) f).IsOver S₀ := by
  constructor
  rw [← comp_over (planeArtinSchreierMap k₀) S₀, artinSchreierPlaneCover.condition_assoc,
    comp_over]
  rfl

/-- The translation `(x, t) ↦ (x, t + a)` of the Artin–Schreier covering by `a ∈ k₀²`. -/
noncomputable def artinSchreierPlaneCover.translation (f : planeIndex → Γ(X, ⊤))
    (a : planeIndex → k₀) : artinSchreierPlaneCover k₀ f ≅ artinSchreierPlaneCover k₀ f where
  hom := pullback.map _ _ _ _ (𝟙 _) (planeTranslation k₀ a).hom (𝟙 _) (by simp) (by simp)
  inv := pullback.map _ _ _ _ (𝟙 _) (planeTranslation k₀ a).inv (𝟙 _) (by simp) (by simp)
  hom_inv_id := by apply pullback.hom_ext <;> simp
  inv_hom_id := by apply pullback.hom_ext <;> simp

/-- The translations of the Artin–Schreier covering lie over `X`. -/
@[reassoc (attr := simp)]
lemma artinSchreierPlaneCover.translation_comp_π (f : planeIndex → Γ(X, ⊤))
    (a : planeIndex → k₀) :
    (artinSchreierPlaneCover.translation f a).hom ≫ artinSchreierPlaneCover.π f =
      artinSchreierPlaneCover.π f := by
  simp [artinSchreierPlaneCover.translation, artinSchreierPlaneCover.π]

/-- The translations of the Artin–Schreier covering translate its coordinates. -/
@[reassoc (attr := simp)]
lemma artinSchreierPlaneCover.translation_comp_coord (f : planeIndex → Γ(X, ⊤))
    (a : planeIndex → k₀) :
    (artinSchreierPlaneCover.translation f a).hom ≫ artinSchreierPlaneCover.coord f =
      artinSchreierPlaneCover.coord f ≫ (planeTranslation k₀ a).hom := by
  simp [artinSchreierPlaneCover.translation, artinSchreierPlaneCover.coord]

instance (f : planeIndex → Γ(X, ⊤)) (a : planeIndex → k₀) :
    (artinSchreierPlaneCover.translation f a).hom.IsOver S₀ := by
  constructor
  change _ ≫ artinSchreierPlaneCover.π f ≫ X ↘ S₀ = artinSchreierPlaneCover.π f ≫ X ↘ S₀
  rw [artinSchreierPlaneCover.translation_comp_π_assoc]

/-- Translation by `a + b` is translation by `a` followed by translation by `b`. -/
lemma artinSchreierPlaneCover.translation_add (f : planeIndex → Γ(X, ⊤))
    (a b : planeIndex → k₀) :
    (artinSchreierPlaneCover.translation f (a + b)).hom =
      (artinSchreierPlaneCover.translation f a).hom ≫
        (artinSchreierPlaneCover.translation f b).hom := by
  apply pullback.hom_ext
  · change _ ≫ artinSchreierPlaneCover.π f = _ ≫ artinSchreierPlaneCover.π f
    simp
  · change _ ≫ artinSchreierPlaneCover.coord f = _ ≫ artinSchreierPlaneCover.coord f
    simp [planeTranslation_add]

variable (k₀) in
/-- The Artin–Schreier covering `π : X' ⟶ X` is a `k₀²`-torsor, as a base change of the
Artin–Schreier map of the plane (`AlgebraicGeometry.isTorsorSplit_planeArtinSchreierMap`). -/
lemma isTorsorSplit_artinSchreierPlaneCover (f : planeIndex → Γ(X, ⊤)) :
    ProEtale.IsTorsorSplit (artinSchreierPlaneCover.π (k₀ := k₀) f)
      (artinSchreierPlaneCover.translation (k₀ := k₀) f)
      (artinSchreierPlaneCover.translation_comp_π (k₀ := k₀) f) :=
  (isTorsorSplit_planeArtinSchreierMap k₀).of_isPullback
    (IsPullback.of_hasPullback (planeSection k₀ f) (planeArtinSchreierMap k₀)).flip _ _
    (artinSchreierPlaneCover.translation_comp_coord f)

instance (f : planeIndex → Γ(X, ⊤)) : Etale (artinSchreierPlaneCover.π (k₀ := k₀) f) :=
  MorphismProperty.pullback_fst _ _ inferInstance

instance (f : planeIndex → Γ(X, ⊤)) : IsFinite (artinSchreierPlaneCover.π (k₀ := k₀) f) :=
  MorphismProperty.pullback_fst _ _ inferInstance

instance (f : planeIndex → Γ(X, ⊤)) : Surjective (artinSchreierPlaneCover.π (k₀ := k₀) f) :=
  MorphismProperty.pullback_fst _ _ inferInstance

instance (f : planeIndex → Γ(X, ⊤)) : QuasiCompact (artinSchreierPlaneCover.π (k₀ := k₀) f) :=
  inferInstance

end Cover

end AlgebraicGeometry
