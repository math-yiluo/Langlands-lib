/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.FiniteFieldDatum.FrobeniusDetailed
import Mathlib.Algebra.CharP.CharAndCard

/-!
# Frobenius squares for an open subscheme over a finite field

Source: Weil conjectures blueprint, `sec-trace-formula/sk-d-weil-push`,
`lem-trf-frobenius-open-square.md`, order 2368; Stacks, Tags 03SM, 01JR and 01JP
(blueprint: lemma-additivity-open-subscheme-complement--1).

The models are arbitrary schemes over the finite base. The scheme Frobenius is written
using `Over.pullback.map` applied to the existing absolute Frobenius; this is the defining
expression of `relativeFrobenius` without its unnecessary finite-type interface.
The Galois maps are the existing unrestricted `galoisMap`. Powers are taken in `End`
of the category of schemes, so the Galois maps are not assumed to be morphisms over `k`.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace WeilConjectures.FiniteFieldDatum

/-- The characteristic of the finite base vanishes on every scheme over that base.
Source: Deligne, Weil II (1.1.14), p. 153; Stacks, Tag 03SM
(blueprint: def-weil-relative-frobenius-geometric-fiber).
Proof: the base has cardinality p^a with a positive, hence characteristic p.
The structure morphism induces a unital map from the base field to global sections,
which takes the equality p = 0 to the asserted equality. This also covers the zero ring. -/
theorem model_characteristic (D : WeilConjectures.FiniteFieldDatum.{u})
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of D.k₀)) :
    (D.p : Γ(X, ⊤)) = 0 := by
  classical
  let _ : Fintype D.k₀ := Fintype.ofFinite D.k₀
  have : Fact D.p.Prime := ⟨D.prime⟩
  have : CharP D.k₀ D.p := charP_of_card_eq_prime_pow
    (by simpa only [Nat.card_eq_fintype_card] using D.card_base.trans D.cardinality_eq)
  let φ := (Scheme.ΓSpecIso (CommRingCat.of D.k₀)).inv ≫ f.appTop
  simpa only [map_natCast, map_zero] using
    congrArg φ.hom (CharP.cast_eq_zero D.k₀ D.p)

/-- The q-power absolute Frobenius of the model is a morphism over the finite base.
Source: Deligne, Weil II (1.1.14), p. 153; Stacks, Tag 0CC7
(blueprint: def-weil-relative-frobenius-geometric-fiber).
Proof: absolute Frobenius is natural in a scheme morphism, by the naturality of taking
p^a-th powers on sections. On Spec k₀ it is the identity because c^q = c in k₀.
Use q = p^a to conclude that its composite with f is f. -/
theorem model_frobenius_over (D : WeilConjectures.FiniteFieldDatum.{u})
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of D.k₀)) :
    X.iterateFrobenius D.prime (D.model_characteristic f) D.a ≫ f = f := by
  classical
  let _ : Fintype D.k₀ := Fintype.ofFinite D.k₀
  apply AlgebraicGeometry.ext_to_Spec
  change (Scheme.ΓSpecIso (CommRingCat.of D.k₀)).inv ≫
      (X.iterateFrobenius D.prime (D.model_characteristic f) D.a ≫ f).appTop = _
  rw [Scheme.Hom.comp_appTop]
  ext x
  change (f.appTop ((Scheme.ΓSpecIso (CommRingCat.of D.k₀)).inv x)) ^
    D.p ^ D.a = f.appTop ((Scheme.ΓSpecIso (CommRingCat.of D.k₀)).inv x)
  rw [← D.cardinality_eq, ← D.card_base, Nat.card_eq_fintype_card, ← map_pow,
    ← map_pow, FiniteField.pow_card]

private theorem pullback_map_eq {S T : Scheme.{u}} (b : T ⟶ S)
    {X Y : Over S} (j : X ⟶ Y) :
    ((Over.pullback b).map j).left =
      pullback.map X.hom b Y.hom b j.left (𝟙 T) (𝟙 S)
        (by simp) (by simp) := by
  apply pullback.hom_ext <;> simp [Over.pullback_map_left, pullback.map]

set_option backward.isDefEq.respectTransparency false in
private theorem pullback_map_range {S T : Scheme.{u}} (b : T ⟶ S)
    {X Y : Over S} (j : X ⟶ Y) :
    Set.range ((Over.pullback b).map j).left =
      pullback.fst Y.hom b ⁻¹' Set.range j.left := by
  rw [pullback_map_eq]
  simpa using Scheme.Pullback.range_map X.hom b Y.hom b j.left (𝟙 T) (𝟙 S)
    (by simp) (by simp)

private theorem pullback_map_open {S T : Scheme.{u}} (b : T ⟶ S)
    {X Y : Over S} (j : X ⟶ Y) [IsOpenImmersion j.left] :
    IsOpenImmersion ((Over.pullback b).map j).left := by
  rw [pullback_map_eq]
  infer_instance

set_option backward.isDefEq.respectTransparency false in
private theorem iterateFrobenius_naturality {X Y : Scheme.{u}} (f : X ⟶ Y)
    {p : ℕ} (hp : p.Prime) (hX : (p : Γ(X, ⊤)) = 0)
    (hY : (p : Γ(Y, ⊤)) = 0) (n : ℕ) :
    X.iterateFrobenius hp hX n ≫ f = f ≫ Y.iterateFrobenius hp hY n := by
  apply Scheme.Hom.ext (by ext x; rfl)
  intro U
  simp only [Scheme.Hom.comp_app]
  change f.app U ≫ (X.iterateFrobenius hp hX n).app (f ⁻¹ᵁ U) ≫
    X.presheaf.map (𝟙 _) =
      (Y.iterateFrobenius hp hY n).app U ≫ f.app U
  rw [X.presheaf.map_id, Category.comp_id]
  ext s
  change ((f.app U).hom s) ^ p ^ n = (f.app U).hom (s ^ p ^ n)
  exact (map_pow (f.app U).hom s _).symm

private theorem isPullback_pow {X Y : Scheme.{u}} {f : X ⟶ X} {g : Y ⟶ Y}
    {j : X ⟶ Y} (h : IsPullback f j j g) (m : ℕ) :
    IsPullback (End.of f ^ m).asHom j j (End.of g ^ m).asHom := by
  induction m with
  | zero => exact IsPullback.of_id_fst
  | succ m ih =>
    simpa only [pow_succ, End.mul_asHom] using h.paste_horiz ih

private theorem semilinear_pow {X S : Scheme.{u}} {f : X ⟶ X} {g : S ⟶ S}
    {a : X ⟶ S} (h : f ≫ a = a ≫ g) (m : ℕ) :
    (End.of f ^ m).asHom ≫ a = a ≫ (End.of g ^ m).asHom := by
  induction m with
  | zero => simp only [pow_zero, End.one_asHom, Category.id_comp, Category.comp_id]
  | succ m ih =>
    rw [pow_succ, pow_succ, End.mul_asHom, End.mul_asHom, Category.assoc, ih,
      ← Category.assoc, h, Category.assoc]

set_option backward.isDefEq.respectTransparency false in
/-- The scheme-Frobenius and geometric-Galois-Frobenius squares of an open immersion
are Cartesian for every nonnegative iterate. The last two identities give semilinearity
of the Galois maps with respect to the projections to `Spec k`.
Source: blueprint `sec-trace-formula/sk-d-weil-push/lem-trf-frobenius-open-square.md`,
order 2368; Stacks, Tags 03SM, 01JR and 01JP
(blueprint: lemma-additivity-open-subscheme-complement--1).

Proof:
1. The structure morphisms make `p` vanish on the models, including empty opens.
   Absolute Frobenius is identity on points and raises sections to `p`-th powers.
   Its `a`-fold iterate therefore raises sections to `q`-th powers. It restricts
   to the same Frobenius on the open subscheme and fixes the finite base field.
2. Its inverse image of the open image of `j₀` is that same open. The inverse-image
   open fibre-product lemma `lem-weil-pbc-open-preimage-fibre-product` identifies
   the model square with a pullback, with exactly these restriction maps.
3. Base change preserves the open immersion by `lem-weil-pbc-open-fibre-product`.
   Compare the two projections to see that the base-changed square commutes.
   Given a compatible pair of maps into it, the model square supplies a unique
   model lift and their common scalar projection supplies the scalar lift.
   The fibre-product universal property then supplies the unique total lift.
4. Geometric field Frobenius fixes the base and has an inverse. Functoriality of
   `Spec` and the fibre product gives inverse coefficient actions on each model's
   scalar extension. Comparing projections shows they commute with `j`. For a
   compatible pair `(u,v)`, the unique lift is the inverse Galois iterate after `u`.
5. The second projection of `id × Spec γ` is the second projection followed by
   `Spec γ`. Iterating proves the two displayed semilinearity identities.
All these arguments include the zeroth iterate, where every endomorphism is identity. -/
theorem frobenius_open_square (D : WeilConjectures.FiniteFieldDatum.{u})
    (X₀ Y₀ : Over (Spec (CommRingCat.of D.k₀))) (j₀ : X₀ ⟶ Y₀)
    [IsOpenImmersion j₀.left] (m : ℕ) :
    IsPullback
      (End.of (((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))).map
        (Over.homMk
          (X₀.left.iterateFrobenius D.prime (D.model_characteristic X₀.hom) D.a)
          (D.model_frobenius_over X₀.hom))).left) ^ m).asHom
      (((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))).map
        j₀).left)
      (((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))).map
        j₀).left)
      (End.of (((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))).map
        (Over.homMk
          (Y₀.left.iterateFrobenius D.prime (D.model_characteristic Y₀.hom) D.a)
          (D.model_frobenius_over Y₀.hom))).left) ^ m).asHom ∧
    IsPullback
      (End.of (D.galoisMap X₀.hom (@FiniteField.geometricFrobeniusAlgEquivOfAlgebraic D.k₀ D.k _
        (Fintype.ofFinite D.k₀) _ _ _)) ^ m).asHom
      (((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))).map
        j₀).left)
      (((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))).map
        j₀).left)
      (End.of (D.galoisMap Y₀.hom (@FiniteField.geometricFrobeniusAlgEquivOfAlgebraic D.k₀ D.k _
        (Fintype.ofFinite D.k₀) _ _ _)) ^ m).asHom ∧
    (End.of (D.galoisMap X₀.hom (@FiniteField.geometricFrobeniusAlgEquivOfAlgebraic D.k₀ D.k _
        (Fintype.ofFinite D.k₀) _ _ _)) ^ m).asHom ≫
        pullback.snd X₀.hom (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k))) =
      pullback.snd X₀.hom (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k))) ≫
        (End.of (Spec.map (CommRingCat.ofHom
          (@FiniteField.geometricFrobeniusAlgEquivOfAlgebraic D.k₀ D.k _
            (Fintype.ofFinite D.k₀) _ _ _).toRingHom)) ^ m).asHom ∧
    (End.of (D.galoisMap Y₀.hom (@FiniteField.geometricFrobeniusAlgEquivOfAlgebraic D.k₀ D.k _
        (Fintype.ofFinite D.k₀) _ _ _)) ^ m).asHom ≫
        pullback.snd Y₀.hom (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k))) =
      pullback.snd Y₀.hom (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k))) ≫
        (End.of (Spec.map (CommRingCat.ofHom
          (@FiniteField.geometricFrobeniusAlgEquivOfAlgebraic D.k₀ D.k _
            (Fintype.ofFinite D.k₀) _ _ _).toRingHom)) ^ m).asHom :=
  by
  let b := Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k))
  let B := Over.pullback b
  let fx : X₀ ⟶ X₀ := Over.homMk
    (X₀.left.iterateFrobenius D.prime (D.model_characteristic X₀.hom) D.a)
    (D.model_frobenius_over X₀.hom)
  let fy : Y₀ ⟶ Y₀ := Over.homMk
    (Y₀.left.iterateFrobenius D.prime (D.model_characteristic Y₀.hom) D.a)
    (D.model_frobenius_over Y₀.hom)
  let j := (B.map j₀).left
  let Fx := (B.map fx).left
  let Fy := (B.map fy).left
  have hn : fx ≫ j₀ = j₀ ≫ fy := by
    apply Over.OverMorphism.ext
    exact iterateFrobenius_naturality j₀.left D.prime
      (D.model_characteristic X₀.hom) (D.model_characteristic Y₀.hom) D.a
  have hc : Fx ≫ j = j ≫ Fy := by
    simpa only [Functor.map_comp, Over.comp_left] using
      congrArg (fun t ↦ (B.map t).left) hn
  have : IsOpenImmersion j := pullback_map_open b j₀
  have hr : Set.range j = pullback.fst Y₀.hom b ⁻¹' Set.range j₀.left :=
    pullback_map_range b j₀
  have hfp (x : (B.obj Y₀).left) :
      pullback.fst Y₀.hom b (Fy x) = pullback.fst Y₀.hom b x := by
    have h : Fy ≫ pullback.fst Y₀.hom b = pullback.fst Y₀.hom b ≫ fy.left := by
      simp [Fy, B, Over.pullback_map_left]
    have hh := congrArg (fun t ↦ t.base.hom x) h
    change pullback.fst Y₀.hom b (Fy x) =
      Y₀.left.iterateFrobenius D.prime (D.model_characteristic Y₀.hom) D.a
        (pullback.fst Y₀.hom b x) at hh
    exact hh
  have hf : IsPullback Fx j j Fy := by
    apply IsOpenImmersion.isPullback Fx j j Fy hc.symm
    apply TopologicalSpace.Opens.ext
    change Fy ⁻¹' Set.range j = Set.range j
    rw [hr]
    ext x
    exact Iff.of_eq (congrArg (fun z ↦ z ∈ Set.range j₀.left) (hfp x))
  refine ⟨isPullback_pow hf m, ?_⟩
  let σ := @FiniteField.geometricFrobeniusAlgEquivOfAlgebraic D.k₀ D.k _
    (Fintype.ofFinite D.k₀) _ _ _
  let gx := D.galoisMap X₀.hom σ
  let gy := D.galoisMap Y₀.hom σ
  have hj₁ : j ≫ pullback.fst Y₀.hom b = pullback.fst X₀.hom b ≫ j₀.left := by
    simp [j, B, Over.pullback_map_left]
  have hj₂ : j ≫ pullback.snd Y₀.hom b = pullback.snd X₀.hom b := by
    simp [j, B, Over.pullback_map_left]
  have hg : gx ≫ j = j ≫ gy := by
    apply pullback.hom_ext
    · calc
        (gx ≫ j) ≫ pullback.fst Y₀.hom b =
            gx ≫ pullback.fst X₀.hom b ≫ j₀.left := by rw [Category.assoc, hj₁]
        _ = pullback.fst X₀.hom b ≫ j₀.left := by
          rw [← Category.assoc, (D.galoisMap_projections X₀.hom σ).1]
        _ = (j ≫ gy) ≫ pullback.fst Y₀.hom b := by
          rw [Category.assoc, (D.galoisMap_projections Y₀.hom σ).1, hj₁]
    · calc
        (gx ≫ j) ≫ pullback.snd Y₀.hom b = gx ≫ pullback.snd X₀.hom b := by
          rw [Category.assoc, hj₂]
        _ = pullback.snd X₀.hom b ≫ Spec.map (CommRingCat.ofHom σ.toRingHom) :=
          (D.galoisMap_projections X₀.hom σ).2
        _ = (j ≫ gy) ≫ pullback.snd Y₀.hom b := by
          rw [Category.assoc, (D.galoisMap_projections Y₀.hom σ).2,
            ← Category.assoc, hj₂]
  have : IsIso gx := by
    exact ⟨⟨D.galoisMap X₀.hom σ.symm,
      (D.galoisMap_inverse X₀.hom σ).1, (D.galoisMap_inverse X₀.hom σ).2⟩⟩
  have : IsIso gy := by
    exact ⟨⟨D.galoisMap Y₀.hom σ.symm,
      (D.galoisMap_inverse Y₀.hom σ).1, (D.galoisMap_inverse Y₀.hom σ).2⟩⟩
  refine ⟨isPullback_pow (IsPullback.of_horiz_isIso ⟨hg⟩) m, ?_, ?_⟩
  · exact semilinear_pow (D.galoisMap_projections X₀.hom σ).2 m
  · exact semilinear_pow (D.galoisMap_projections Y₀.hom σ).2 m

end WeilConjectures.FiniteFieldDatum
