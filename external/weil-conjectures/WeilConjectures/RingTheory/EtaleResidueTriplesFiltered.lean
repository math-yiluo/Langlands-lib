/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.EtaleResidueTriples
public import Mathlib.CategoryTheory.Filtered.Basic
import Mathlib.AlgebraicGeometry.Pullbacks

/-!
# Filteredness of étale residue triples over an arbitrary field

Source: Stacks Project, Tag 04GW, filteredness argument in Lemma 10.155.11.
The argument uses only the fixed residue-field embedding, not separable closedness.
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme

private lemma spec_map_point (B : CommRingCat.{u}) (q : Spec B)
    (K : Type u) [Field K] (φ : (Spec B).residueField q ⟶ CommRingCat.of K) :
    Spec.map ((ΓSpecIso B).inv ≫ (Spec B).Γevaluation q ≫ φ) =
      Spec.map φ ≫ (Spec B).fromSpecResidueField q := by
  simp only [fromSpecResidueField, Spec.fromSpecStalk_eq, ← Spec.map_comp]
  rfl

private lemma exists_pointing (B : CommRingCat.{u}) (K : Type u) [Field K]
    (b : B ⟶ CommRingCat.of K) :
    ∃ (q : Spec B) (φ : (Spec B).residueField q ⟶ CommRingCat.of K),
      (ΓSpecIso B).inv ≫ (Spec B).Γevaluation q ≫ φ = b := by
  generalize he : (SpecToEquivOfField K (Spec B)) (Spec.map b) = z
  obtain ⟨q, φ⟩ := z
  refine ⟨q, φ, ?_⟩
  apply Spec.map_injective
  rw [spec_map_point]
  have h := (SpecToEquivOfField K (Spec B)).symm_apply_apply (Spec.map b)
  rw [he] at h
  exact h

private lemma pointing_over (R B : CommRingCat.{u}) (p : Spec R)
    (K : Type u) [Field K] (χ : (Spec R).residueField p ⟶ CommRingCat.of K)
    (a : R ⟶ B) (q : Spec B) (φ : (Spec B).residueField q ⟶ CommRingCat.of K)
    (hc : a ≫ (ΓSpecIso B).inv ≫ (Spec B).Γevaluation q ≫ φ =
      (ΓSpecIso R).inv ≫ (Spec R).Γevaluation p ≫ χ) :
    Spec.map a q = p := by
  have h := congrArg Spec.map hc
  rw [Spec.map_comp, spec_map_point, spec_map_point] at h
  have h' := congrArg (fun f : Spec (CommRingCat.of K) ⟶ Spec R ↦ f (IsLocalRing.closedPoint K)) h
  simpa using h'

private lemma etale_pushout_inr {A B C : CommRingCat.{u}} (f : A ⟶ B) (g : A ⟶ C)
    (hf : AlgebraicGeometry.Etale (Spec.map f)) :
    AlgebraicGeometry.Etale (Spec.map (Limits.pushout.inr f g)) := by
  exact MorphismProperty.of_isPullback (isPullback_SpecMap_pushout f g) hf

private lemma etale_pushout_inl {A B C : CommRingCat.{u}} (f : A ⟶ B) (g : A ⟶ C)
    (hg : AlgebraicGeometry.Etale (Spec.map g)) :
    AlgebraicGeometry.Etale (Spec.map (Limits.pushout.inl f g)) := by
  exact MorphismProperty.of_isPullback (isPullback_SpecMap_pushout f g).flip hg

private lemma etale_comp {A B C : CommRingCat.{u}} (f : A ⟶ B) (g : B ⟶ C)
    (hf : AlgebraicGeometry.Etale (Spec.map f))
    (hg : AlgebraicGeometry.Etale (Spec.map g)) :
    AlgebraicGeometry.Etale (Spec.map (f ≫ g)) := by
  let := hf
  let := hg
  rw [Spec.map_comp]
  infer_instance

private lemma etale_cancel {A B C : CommRingCat.{u}} (a : A ⟶ B) (b : A ⟶ C)
    (f : B ⟶ C) (ha : AlgebraicGeometry.Etale (Spec.map a))
    (hb : AlgebraicGeometry.Etale (Spec.map b)) (hw : a ≫ f = b) :
    AlgebraicGeometry.Etale (Spec.map f) := by
  let := ha
  have h : AlgebraicGeometry.Etale (Spec.map f ≫ Spec.map a) := by
    rw [← Spec.map_comp, hw]
    exact hb
  let := h
  exact AlgebraicGeometry.Etale.of_comp (Spec.map f) (Spec.map a)

private noncomputable def tripleOfMap {R : CommRingCat.{u}} {p : Spec R}
    {K : Type u} [Field K] {χ : (Spec R).residueField p ⟶ CommRingCat.of K}
    (B : CommRingCat.{u}) (a : R ⟶ B) (b : B ⟶ CommRingCat.of K)
    (ha : AlgebraicGeometry.Etale (Spec.map a))
    (hc : a ≫ b = (ΓSpecIso R).inv ≫ (Spec R).Γevaluation p ≫ χ) :
    EtaleResidueTriples R p K χ := by
  let q := (exists_pointing B K b).choose
  let φ := (exists_pointing B K b).choose_spec.choose
  have hφ := (exists_pointing B K b).choose_spec.choose_spec
  exact { B := B
          α := a
          etale := ha
          q := q
          over := pointing_over R B p K χ a q φ (by rw [hφ, hc])
          φ := φ
          compatible := by rw [hφ, hc] }

private lemma tripleOfMap_point {R : CommRingCat.{u}} {p : Spec R}
    {K : Type u} [Field K] {χ : (Spec R).residueField p ⟶ CommRingCat.of K}
    (B : CommRingCat.{u}) (a : R ⟶ B) (b : B ⟶ CommRingCat.of K)
    (ha : AlgebraicGeometry.Etale (Spec.map a))
    (hc : a ≫ b = (ΓSpecIso R).inv ≫ (Spec R).Γevaluation p ≫ χ) :
    let t := tripleOfMap B a b ha hc
    (ΓSpecIso t.B).inv ≫ (Spec t.B).Γevaluation t.q ≫ t.φ = b := by
  exact (exists_pointing B K b).choose_spec.choose_spec

private noncomputable def tripleHom {R : CommRingCat.{u}} {p : Spec R}
    {K : Type u} [Field K] {χ : (Spec R).residueField p ⟶ CommRingCat.of K}
    {s t : EtaleResidueTriples R p K χ} (f : s.B ⟶ t.B) (ha : s.α ≫ f = t.α)
    (hb : f ≫ (ΓSpecIso t.B).inv ≫ (Spec t.B).Γevaluation t.q ≫ t.φ =
      (ΓSpecIso s.B).inv ≫ (Spec s.B).Γevaluation s.q ≫ s.φ) : s ⟶ t :=
  InducedCategory.homMk (Under.homMk (Over.homMk f hb) (by
    apply Over.OverMorphism.ext
    exact ha))

/-- Étale residue triples are filtered for any field with a fixed residue-field embedding.
Source: Stacks Project, Tag 04GW, first three paragraphs of the proof of Lemma 10.155.11.

Proof: The identity triple `(R, p, χ)` gives nonemptiness. For two triples with rings
`S` and `T`, their maps to `K` agree on `R`, so induce a map `S ⊗[R] T → K`.
Its kernel is a prime over both pointed primes; extension to its residue field gives
an embedding in `K`. Base change and composition show that this tensor product is
étale over `R`, giving a common successor. For parallel maps `β₁, β₂ : S → T`, form
`E = T ⊗[S] T` using these maps and `U = E ⊗[T ⊗[R] T] T` using multiplication.
Maps between étale `R`-algebras are étale, as is their diagonal; hence the needed
base changes and composites are étale. The map `T → K` extends to `U` because it
agrees after `β₁` and `β₂`. Its kernel and residue-field extension give another triple.
The rightmost map `T → U` respects the pointing and equalizes the parallel maps:
the tensor relation in `E` identifies `β₁(s) ⊗ 1` with `1 ⊗ β₂(s)`, and the final
base change identifies these with their images from the rightmost `T`.
These are the three filteredness conditions. No closure or algebraicity property of
`K` is used. The identity triple also covers the case `K = κ(p)`.
(blueprint: lem-weil-pbc-etale-triples-filtered-colimit-filtered) -/
theorem etaleResidueTriples_filtered_part
    (R : CommRingCat.{u}) (p : Spec R) (K : Type u) [Field K]
    (χ : (Spec R).residueField p ⟶ CommRingCat.of K) :
    IsFiltered (EtaleResidueTriples R p K χ) := by
  classical
  refine { nonempty := ?nonempty, cocone_objs := ?cocone_objs, cocone_maps := ?cocone_maps }
  case nonempty =>
    refine ⟨{ B := R
              α := 𝟙 R
              etale := ?_
              q := p
              over := by simp
              φ := χ
              compatible := by simp }⟩
    simpa using (inferInstance : AlgebraicGeometry.Etale (𝟙 (Spec R)))
  case cocone_objs =>
    intro s t
    let bs := (ΓSpecIso s.B).inv ≫ (Spec s.B).Γevaluation s.q ≫ s.φ
    let bt := (ΓSpecIso t.B).inv ≫ (Spec t.B).Γevaluation t.q ≫ t.φ
    have hst : s.α ≫ bs = t.α ≫ bt := s.compatible.trans t.compatible.symm
    let P := Limits.pushout s.α t.α
    let a : R ⟶ P := s.α ≫ Limits.pushout.inl s.α t.α
    let b : P ⟶ CommRingCat.of K := Limits.pushout.desc bs bt hst
    have ha : AlgebraicGeometry.Etale (Spec.map a) :=
      etale_comp _ _ s.etale (etale_pushout_inl s.α t.α t.etale)
    have hc : a ≫ b = (ΓSpecIso R).inv ≫ (Spec R).Γevaluation p ≫ χ := by
      dsimp only [a, b]
      rw [Category.assoc, Limits.pushout.inl_desc]
      exact s.compatible
    let z := tripleOfMap P a b ha hc
    have hz := tripleOfMap_point P a b ha hc
    refine ⟨z, tripleHom (Limits.pushout.inl s.α t.α) rfl ?_,
      tripleHom (Limits.pushout.inr s.α t.α) ?_ ?_, trivial⟩
    · rw [hz]
      exact Limits.pushout.inl_desc _ _ _
    · exact (Limits.pushout.condition (f := s.α) (g := t.α)).symm
    · rw [hz]
      exact Limits.pushout.inr_desc _ _ _
  case cocone_maps =>
    intro s t f g
    let bs := (ΓSpecIso s.B).inv ≫ (Spec s.B).Γevaluation s.q ≫ s.φ
    let bt := (ΓSpecIso t.B).inv ≫ (Spec t.B).Γevaluation t.q ≫ t.φ
    let f₀ : s.B ⟶ t.B := f.hom.right.left
    let g₀ : s.B ⟶ t.B := g.hom.right.left
    have hf : s.α ≫ f₀ = t.α := congrArg CommaMorphism.left (Under.w f.hom)
    have hg : s.α ≫ g₀ = t.α := congrArg CommaMorphism.left (Under.w g.hom)
    have hfb : f₀ ≫ bt = bs := Over.w f.hom.right
    have hgb : g₀ ≫ bt = bs := Over.w g.hom.right
    -- These pushouts realize T ⊗[S] T and T ⊗[R] T.
    let E := Limits.pushout f₀ g₀
    let P := Limits.pushout t.α t.α
    let l : t.B ⟶ E := Limits.pushout.inl f₀ g₀
    let r : t.B ⟶ E := Limits.pushout.inr f₀ g₀
    have hR : t.α ≫ l = t.α ≫ r := by
      calc
        t.α ≫ l = (s.α ≫ f₀) ≫ l := by rw [hf]
        _ = (s.α ≫ g₀) ≫ r := by
          rw [Category.assoc, Category.assoc]
          exact congrArg (s.α ≫ ·) Limits.pushout.condition
        _ = t.α ≫ r := by rw [hg]
    let m : P ⟶ E := Limits.pushout.desc l r hR
    let d : P ⟶ t.B := Limits.pushout.desc (𝟙 _) (𝟙 _) (by simp)
    -- Base change along multiplication identifies both T factors in U.
    let U := Limits.pushout m d
    let k : E ⟶ U := Limits.pushout.inl m d
    let h : t.B ⟶ U := Limits.pushout.inr m d
    have hl : l ≫ k = h := by
      have hw := congrArg (Limits.pushout.inl t.α t.α ≫ ·)
        (Limits.pushout.condition (f := m) (g := d))
      simpa only [Category.assoc, m, d, Limits.pushout.inl_desc_assoc,
        Category.id_comp] using hw
    have hr : r ≫ k = h := by
      have hw := congrArg (Limits.pushout.inr t.α t.α ≫ ·)
        (Limits.pushout.condition (f := m) (g := d))
      simpa only [Category.assoc, m, d, Limits.pushout.inr_desc_assoc,
        Category.id_comp] using hw
    have heq : f₀ ≫ h = g₀ ≫ h := by
      calc
        f₀ ≫ h = (f₀ ≫ l) ≫ k := by rw [Category.assoc, hl]
        _ = (g₀ ≫ r) ≫ k := congrArg (· ≫ k) Limits.pushout.condition
        _ = g₀ ≫ h := by rw [Category.assoc, hr]
    let e : E ⟶ CommRingCat.of K := Limits.pushout.desc bt bt (hfb.trans hgb.symm)
    have hmd : m ≫ e = d ≫ bt := by
      apply Limits.pushout.hom_ext <;> simp [m, d, e, l, r]
    let b : U ⟶ CommRingCat.of K := Limits.pushout.desc e bt hmd
    have hb : h ≫ b = bt := Limits.pushout.inr_desc _ _ _
    have hfet : AlgebraicGeometry.Etale (Spec.map f₀) :=
      etale_cancel s.α t.α f₀ s.etale t.etale hf
    have hret : AlgebraicGeometry.Etale (Spec.map r) :=
      etale_pushout_inr f₀ g₀ hfet
    have hPet : AlgebraicGeometry.Etale
        (Spec.map (t.α ≫ Limits.pushout.inl t.α t.α)) :=
      etale_comp _ _ t.etale (etale_pushout_inl t.α t.α t.etale)
    have hdet : AlgebraicGeometry.Etale (Spec.map d) :=
      etale_cancel (t.α ≫ Limits.pushout.inl t.α t.α) t.α d hPet t.etale (by simp [d])
    have hket : AlgebraicGeometry.Etale (Spec.map k) := etale_pushout_inl m d hdet
    have hhet : AlgebraicGeometry.Etale (Spec.map h) := by
      rw [← hr]
      exact etale_comp r k hret hket
    have ha : AlgebraicGeometry.Etale (Spec.map (t.α ≫ h)) :=
      etale_comp _ _ t.etale hhet
    have hc : (t.α ≫ h) ≫ b =
        (ΓSpecIso R).inv ≫ (Spec R).Γevaluation p ≫ χ := by
      rw [Category.assoc, hb]
      exact t.compatible
    let z := tripleOfMap U (t.α ≫ h) b ha hc
    have hz := tripleOfMap_point U (t.α ≫ h) b ha hc
    let h' : t ⟶ z := tripleHom h rfl (by rw [hz]; exact hb)
    refine ⟨z, h', ?_⟩
    apply InducedCategory.hom_ext
    apply Under.UnderMorphism.ext
    apply Over.OverMorphism.ext
    exact heq

end AlgebraicGeometry.Scheme
