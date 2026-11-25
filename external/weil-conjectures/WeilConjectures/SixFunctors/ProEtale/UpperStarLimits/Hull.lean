/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.RingTheory.ProEtale.ClosedLiftWeaklyEtale
public import WeilConjectures.SixFunctors.ProEtale.UpperStarLimits.AffineCoversSplit

/-!
# Weakly étale hulls of affine schemes with split affine covers

Let `h : X ⟶ Y` be a morphism of schemes. A *weakly étale hull* of `h`
(`AlgebraicGeometry.Scheme.ProEt.IsHull`) is a factorization `X ⟶ W₀ ⟶ Y` through an object
`W₀` of the small pro-étale site of `Y` which is initial among such factorizations: every
factorization `X ⟶ W ⟶ Y` with `W ⟶ Y` weakly étale is obtained from it by a unique morphism
`W₀ ⟶ W` over `Y`.

`AlgebraicGeometry.Scheme.ProEt.exists_isHull`: if `X` is affine with split affine covers (e.g.
the spectrum of a w-contractible ring) and `Y = Spec B` is affine, a hull exists. With
`X = Spec A`, it is `W₀ = Spec H_B(A)`, where `H_B(A)` is the colimit of the étale `B`-algebras
mapping to `A` (`Algebra.ClosedLift`); see Bhatt–Scholze, *The pro-étale topology for schemes*,
§2.2.

- Every morphism `X ⟶ T` to an affine scheme `T` weakly étale over `Spec B` factors through
  `W₀`, by the universal property of `H_B(A)` for weakly étale `B`-algebras
  (`Algebra.ClosedLift.exists_comp_toAlgHom_eq_of_weaklyEtale`); for a general `W`, a morphism
  `X ⟶ W` factors through an affine scheme weakly étale over `W`
  (`AlgebraicGeometry.Scheme.AffineCoversSplit.exists_factorization`).
- Endomorphisms of `W₀` under `X` are trivial, `H_B(A)` being ind-étale over `B`. Two
  factorizations `W₀ ⟶ W` agree: their equalizer `E ⟶ W₀` (a base change of the weakly étale
  diagonal of `W`) receives a morphism `W₀ ⟶ E` under `X`, which is a section of `E ⟶ W₀`.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.Scheme.ProEt

/-- A *weakly étale hull* of `h : X ⟶ Y`: a factorization `ψ : X ⟶ W₀`, `W₀ ⟶ Y` of `h` through an
object `W₀` of the small pro-étale site of `Y`, such that every factorization `φ : X ⟶ W`,
`W ⟶ Y` through an object of `Y_proét` is `ψ` followed by a unique morphism `W₀ ⟶ W` of
`Y_proét`. -/
def IsHull {X Y : Scheme.{u}} (h : X ⟶ Y) (W₀ : Y.ProEt) (ψ : X ⟶ W₀.left) : Prop :=
  ψ ≫ W₀.hom = h ∧
    ∀ (W : Y.ProEt) (φ : X ⟶ W.left), φ ≫ W.hom = h → ∃! t : W₀ ⟶ W, ψ ≫ t.left = φ

/-- Hulls can be transported along isomorphisms of the source. -/
lemma IsHull.of_iso {X X' Y : Scheme.{u}} {h : X ⟶ Y} {W₀ : Y.ProEt} {ψ : X ⟶ W₀.left}
    (hψ : IsHull h W₀ ψ) (e : X' ≅ X) : IsHull (e.hom ≫ h) W₀ (e.hom ≫ ψ) := by
  refine ⟨by rw [Category.assoc, hψ.1], fun W φ hφ ↦ ?_⟩
  obtain ⟨t, ht, hu⟩ := hψ.2 W (e.inv ≫ φ) (by rw [Category.assoc, hφ, Iso.inv_hom_id_assoc])
  refine ⟨t, ?_, fun t' ht' ↦ hu t' ?_⟩
  · dsimp only
    rw [Category.assoc, ht, Iso.hom_inv_id_assoc]
  · dsimp only at ht' ⊢
    rw [← ht', Category.assoc, Iso.inv_hom_id_assoc]

section Spec

variable (B : CommRingCat.{u}) (A : Type u) [CommRing A] [Algebra B A]

/-- The hull `Spec H_B(A)`, as an object of the small pro-étale site of `Spec B`. -/
noncomputable def hullSpec : (Spec B).ProEt :=
  Scheme.ProEt.mk (Spec.map (CommRingCat.ofHom (algebraMap B (Algebra.ClosedLift B A))))

lemma hullSpec_hom :
    (hullSpec B A).hom = Spec.map (CommRingCat.ofHom (algebraMap B (Algebra.ClosedLift B A))) :=
  rfl

/-- The morphism `Spec A ⟶ Spec H_B(A)` induced by `H_B(A) ⟶ A`. -/
noncomputable def toHullSpec : Spec (.of A) ⟶ (hullSpec B A).left :=
  Spec.map (CommRingCat.ofHom (Algebra.ClosedLift.toAlgHom B A).toRingHom)

lemma toHullSpec_comp_hom :
    toHullSpec B A ≫ (hullSpec B A).hom = Spec.map (CommRingCat.ofHom (algebraMap B A)) := by
  rw [toHullSpec, hullSpec_hom, ← Spec.map_comp]
  congr 1
  ext b
  exact (Algebra.ClosedLift.toAlgHom B A).commutes b

variable {B A}

/-- An endomorphism of `Spec H_B(A)` over `Spec B` and under `Spec A` is the identity. -/
lemma eq_id_of_toHullSpec_comp_eq (t : (hullSpec B A).left ⟶ (hullSpec B A).left)
    (ht : t ≫ (hullSpec B A).hom = (hullSpec B A).hom) (ht' : toHullSpec B A ≫ t = toHullSpec B A) :
    t = 𝟙 _ := by
  let τ := Spec.preimage t
  have h₁ : CommRingCat.ofHom (algebraMap B (Algebra.ClosedLift B A)) ≫ τ =
      CommRingCat.ofHom (algebraMap B (Algebra.ClosedLift B A)) :=
    Spec.map_injective (by rw [Spec.map_comp, Spec.map_preimage]; exact ht)
  have h₂ : τ ≫ CommRingCat.ofHom (Algebra.ClosedLift.toAlgHom B A).toRingHom =
      CommRingCat.ofHom (Algebra.ClosedLift.toAlgHom B A).toRingHom :=
    Spec.map_injective (by rw [Spec.map_comp, Spec.map_preimage]; exact ht')
  let f : Algebra.ClosedLift B A →ₐ[B] Algebra.ClosedLift B A :=
    { τ.hom with commutes' := fun b ↦ congrArg (fun φ ↦ φ.hom b) h₁ }
  have hf := Algebra.ClosedLift.eq_id_of_toAlgHom_comp_eq f
    (AlgHom.ext fun x ↦ congrArg (fun φ ↦ φ.hom x) h₂)
  have hτ : τ = 𝟙 _ := by
    ext x
    exact DFunLike.congr_fun hf x
  rw [← Spec.map_preimage t]
  change Spec.map τ = _
  rw [hτ, Spec.map_id]
  rfl

variable (hA : ∀ (T : Type u) [CommRing T] [Algebra A T] [Algebra.IndEtale A T]
  [Module.FaithfullyFlat A T], ∃ f : T →+* A, f.comp (algebraMap A T) = RingHom.id A)
include hA

/-- A morphism `Spec A ⟶ T` over `Spec B` to an affine scheme `T` weakly étale over `Spec B`
factors through `Spec H_B(A)`. -/
lemma exists_toHullSpec_comp_eq_of_isAffine {T : Scheme.{u}} [IsAffine T] (p : T ⟶ Spec B)
    [WeaklyEtale p] (φ : Spec (.of A) ⟶ T)
    (hφ : φ ≫ p = Spec.map (CommRingCat.ofHom (algebraMap B A))) :
    ∃ t : (hullSpec B A).left ⟶ T, t ≫ p = (hullSpec B A).hom ∧ toHullSpec B A ≫ t = φ := by
  let eT := T.isoSpec
  let π : B ⟶ Γ(T, ⊤) := Spec.preimage (eT.inv ≫ p)
  let χ : Γ(T, ⊤) ⟶ CommRingCat.of A := Spec.preimage (φ ≫ eT.hom)
  let : Algebra B Γ(T, ⊤) := π.hom.toAlgebra
  have : Algebra.WeaklyEtale B Γ(T, ⊤) := by
    rw [← weaklyEtale_SpecMap_algebraMap_iff]
    change WeaklyEtale (Spec.map π)
    rw [Spec.map_preimage]
    infer_instance
  have hχ : π ≫ χ = CommRingCat.ofHom (algebraMap B A) := Spec.map_injective (by
    rw [Spec.map_comp, Spec.map_preimage, Spec.map_preimage, Category.assoc,
      Iso.hom_inv_id_assoc, hφ])
  let q : Γ(T, ⊤) →ₐ[B] A :=
    { χ.hom with commutes' := fun b ↦ congrArg (fun φ ↦ φ.hom b) hχ }
  obtain ⟨f, hf⟩ := Algebra.ClosedLift.exists_comp_toAlgHom_eq_of_weaklyEtale hA q
  refine ⟨Spec.map (CommRingCat.ofHom f.toRingHom) ≫ eT.inv, ?_, ?_⟩
  · have : eT.inv ≫ p = Spec.map π := (Spec.map_preimage _).symm
    rw [Category.assoc, this, ← Spec.map_comp, hullSpec_hom]
    congr 1
    ext b
    exact f.commutes b
  · have : CommRingCat.ofHom f.toRingHom ≫
        CommRingCat.ofHom (Algebra.ClosedLift.toAlgHom B A).toRingHom = χ := by
      ext x
      exact DFunLike.congr_fun hf x
    rw [toHullSpec, ← Category.assoc, ← Spec.map_comp, this, Spec.map_preimage, Category.assoc,
      Iso.hom_inv_id, Category.comp_id]

/-- A morphism `Spec A ⟶ W.left` over `Spec B` to any object `W` of the small pro-étale site of
`Spec B` factors through `Spec H_B(A)`. -/
lemma exists_toHullSpec_comp_eq (W : (Spec B).ProEt) (φ : Spec (.of A) ⟶ W.left)
    (hφ : φ ≫ W.hom = Spec.map (CommRingCat.ofHom (algebraMap B A))) :
    ∃ t : hullSpec B A ⟶ W, toHullSpec B A ≫ t.left = φ := by
  obtain ⟨T, _, a, b, hb, hab⟩ :=
    (affineCoversSplit_Spec (R := .of A) hA).exists_factorization φ
  obtain ⟨t₀, ht₀, ht₀'⟩ := exists_toHullSpec_comp_eq_of_isAffine hA (b ≫ W.hom) a
    (by rw [← Category.assoc, hab, hφ])
  refine ⟨MorphismProperty.Over.homMk (t₀ ≫ b) (by rw [Category.assoc]; exact ht₀) trivial, ?_⟩
  exact (Category.assoc _ _ _).symm.trans (by rw [ht₀', hab])

/-- Two morphisms `Spec H_B(A) ⟶ W` of the small pro-étale site of `Spec B` which agree under
`Spec A` are equal: the equalizer `E ⟶ Spec H_B(A)` is weakly étale, being a base change of the
diagonal of `W`, so it receives a morphism `Spec H_B(A) ⟶ E` under `Spec A`, which is a section
of `E ⟶ Spec H_B(A)` by `eq_id_of_toHullSpec_comp_eq`. -/
lemma hom_ext_of_toHullSpec_comp {W : (Spec B).ProEt} (t₁ t₂ : hullSpec B A ⟶ W)
    (h : toHullSpec B A ≫ t₁.left = toHullSpec B A ≫ t₂.left) : t₁ = t₂ := by
  have hw : t₁.left ≫ W.hom = t₂.left ≫ W.hom := by
    rw [MorphismProperty.Over.w t₁, MorphismProperty.Over.w t₂]
  let l : (hullSpec B A).left ⟶ pullback W.hom W.hom := pullback.lift t₁.left t₂.left hw
  let e : pullback (pullback.diagonal W.hom) l ⟶ (hullSpec B A).left := pullback.snd _ _
  let w : pullback (pullback.diagonal W.hom) l ⟶ W.left := pullback.fst _ _
  have he₁ : e ≫ t₁.left = w := by
    have := congrArg (· ≫ pullback.fst W.hom W.hom)
      (pullback.condition (f := pullback.diagonal W.hom) (g := l))
    simpa [l, e, w] using this.symm
  have he₂ : e ≫ t₂.left = w := by
    have := congrArg (· ≫ pullback.snd W.hom W.hom)
      (pullback.condition (f := pullback.diagonal W.hom) (g := l))
    simpa [l, e, w] using this.symm
  let E : (Spec B).ProEt := Scheme.ProEt.mk (e ≫ (hullSpec B A).hom)
  have hl : (toHullSpec B A ≫ t₁.left) ≫ pullback.diagonal W.hom = toHullSpec B A ≫ l := by
    apply pullback.hom_ext
    · simp [l]
    · simp [l, h]
  let ψE : Spec (.of A) ⟶ E.left := pullback.lift _ _ hl
  have hψE : ψE ≫ e = toHullSpec B A := pullback.lift_snd _ _ _
  obtain ⟨t, ht⟩ := exists_toHullSpec_comp_eq hA E ψE (by
    rw [ProEt.mk_hom, ← Category.assoc, hψE, toHullSpec_comp_hom])
  have hte : t.left ≫ e = 𝟙 _ := by
    refine eq_id_of_toHullSpec_comp_eq _ ?_ ?_
    · rw [Category.assoc]
      exact MorphismProperty.Over.w t
    · rw [← Category.assoc, ht, hψE]
  refine MorphismProperty.Over.Hom.ext ?_
  calc t₁.left = (t.left ≫ e) ≫ t₁.left := by rw [hte, Category.id_comp]
    _ = (t.left ≫ e) ≫ t₂.left := by rw [Category.assoc, Category.assoc, he₁, he₂]
    _ = t₂.left := by rw [hte, Category.id_comp]

/-- **The hull of `Spec A ⟶ Spec B`.** If every faithfully flat ind-étale `A`-algebra has a
retraction, `Spec A ⟶ Spec H_B(A) ⟶ Spec B` is a weakly étale hull of `Spec A ⟶ Spec B`. -/
theorem isHull_hullSpec :
    IsHull (Spec.map (CommRingCat.ofHom (algebraMap B A))) (hullSpec B A) (toHullSpec B A) := by
  refine ⟨toHullSpec_comp_hom B A, fun W φ hφ ↦ ?_⟩
  obtain ⟨t, ht⟩ := exists_toHullSpec_comp_eq hA W φ hφ
  exact ⟨t, ht, fun t' ht' ↦ hom_ext_of_toHullSpec_comp hA t' t (ht'.trans ht.symm)⟩

end Spec

/-- **Existence of weakly étale hulls.** Every morphism `h : X ⟶ Spec B` from an affine scheme
with split affine covers (e.g. the spectrum of a w-contractible ring) has a weakly étale hull. -/
theorem exists_isHull {X : Scheme.{u}} [IsAffine X] (hX : AffineCoversSplit X)
    {B : CommRingCat.{u}} (h : X ⟶ Spec B) : ∃ W₀ ψ, IsHull h W₀ ψ := by
  let e := X.isoSpec
  let φ : B ⟶ Γ(X, ⊤) := Spec.preimage (e.inv ≫ h)
  let : Algebra B Γ(X, ⊤) := φ.hom.toAlgebra
  have hA := (hX.of_iso e).exists_retraction
  have hψ := (isHull_hullSpec (B := B) (A := Γ(X, ⊤)) hA).of_iso e
  have : e.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap B Γ(X, ⊤))) = h := by
    change e.hom ≫ Spec.map φ = h
    rw [Spec.map_preimage, Iso.hom_inv_id_assoc]
  rw [this] at hψ
  exact ⟨_, _, hψ⟩

/-- **Hulls of disjoint unions.** Let `X = ∐ Tᵢ` and let `(W₀, ψ)` be a hull of `h : X ⟶ Y` and
`(Wᵢ, ψᵢ)` hulls of the restrictions `Tᵢ ⟶ X ⟶ Y`. Then the induced morphisms `sᵢ : Wᵢ ⟶ W₀`
exhibit `W₀` as the disjoint union of the `Wᵢ`: the coproduct `∐ Wᵢ` is weakly étale over `Y`,
and the universal properties of the hulls give mutually inverse morphisms `W₀ ⟶ ∐ Wᵢ` and
`∐ Wᵢ ⟶ W₀`. -/
lemma nonempty_isColimit_cofan_of_isHull {X Y : Scheme.{u}} {ι : Type u} {T : ι → Scheme.{u}}
    (f : ∀ i, T i ⟶ X) (hf : IsColimit (Cofan.mk X f)) (h : X ⟶ Y) {W₀ : Y.ProEt}
    {ψ : X ⟶ W₀.left} (hψ : IsHull h W₀ ψ) {W : ι → Y.ProEt} {ψ' : ∀ i, T i ⟶ (W i).left}
    (hψ' : ∀ i, IsHull (f i ≫ h) (W i) (ψ' i)) (s : ∀ i, W i ⟶ W₀)
    (hs : ∀ i, ψ' i ≫ (s i).left = f i ≫ ψ) :
    Nonempty (IsColimit (Cofan.mk W₀.left fun i ↦ (s i).left)) := by
  have : WeaklyEtale (Sigma.desc fun i ↦ (W i).hom) :=
    IsZariskiLocalAtSource.sigmaDesc fun i ↦ inferInstance
  let Wsum : Y.ProEt := Scheme.ProEt.mk (Sigma.desc fun i ↦ (W i).hom)
  let φsum : X ⟶ Wsum.left := Cofan.IsColimit.desc hf fun i ↦ ψ' i ≫ Sigma.ι (fun i ↦ (W i).left) i
  have hφsum (i : ι) : f i ≫ φsum = ψ' i ≫ Sigma.ι (fun i ↦ (W i).left) i :=
    Cofan.IsColimit.fac hf _ i
  obtain ⟨t, ht, -⟩ := hψ.2 Wsum φsum (Cofan.IsColimit.hom_ext hf _ _ fun i ↦ by
    rw [cofan_mk_inj, ← Category.assoc, hφsum, ProEt.mk_hom, Category.assoc,
      Sigma.ι_comp_desc, (hψ' i).1])
  let ssum : Wsum ⟶ W₀ := MorphismProperty.Over.homMk (Sigma.desc fun i ↦ (s i).left)
    (Sigma.hom_ext _ _ fun i ↦ by
      rw [Sigma.ι_comp_desc_assoc, MorphismProperty.Over.w (s i),
        ProEt.mk_hom, Sigma.ι_comp_desc]) trivial
  have h₁ : t ≫ ssum = 𝟙 W₀ := by
    refine (hψ.2 W₀ ψ hψ.1).unique ?_ (Category.comp_id _)
    refine Cofan.IsColimit.hom_ext hf _ _ fun i ↦ ?_
    change f i ≫ ψ ≫ t.left ≫ Sigma.desc (fun i ↦ (s i).left) = f i ≫ ψ
    rw [← Category.assoc ψ, ht, ← Category.assoc, hφsum, Category.assoc, Sigma.ι_comp_desc, hs]
  have h₂ : ssum ≫ t = 𝟙 Wsum := by
    refine MorphismProperty.Over.Hom.ext (Sigma.hom_ext _ _ fun i ↦ ?_)
    let ιsum : W i ⟶ Wsum := MorphismProperty.Over.homMk (Sigma.ι (fun i ↦ (W i).left) i)
      (by rw [ProEt.mk_hom, Sigma.ι_comp_desc]) trivial
    have hu := ((hψ' i).2 Wsum (ψ' i ≫ Sigma.ι (fun i ↦ (W i).left) i) (by
      rw [Category.assoc, ProEt.mk_hom, Sigma.ι_comp_desc, (hψ' i).1])).unique
      (y₁ := s i ≫ t) (y₂ := ιsum) (by
        change ψ' i ≫ (s i).left ≫ t.left = _
        rw [← Category.assoc, hs, Category.assoc, ht, hφsum]) rfl
    exact (Sigma.ι_comp_desc_assoc _ _ _).trans
      ((congrArg (fun m ↦ m.left) hu).trans (Category.comp_id _).symm)
  have : IsIso (Sigma.desc fun i ↦ (s i).left) :=
    ⟨⟨t.left, congrArg (fun m ↦ m.left) h₂, congrArg (fun m ↦ m.left) h₁⟩⟩
  exact (Cofan.nonempty_isColimit_iff_isIso_sigmaDesc _).2 this

end AlgebraicGeometry.Scheme.ProEt
