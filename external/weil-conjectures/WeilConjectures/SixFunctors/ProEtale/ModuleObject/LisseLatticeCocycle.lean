/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.Adic.LisseCover.RegularLattice
public import WeilConjectures.SixFunctors.ProEtale.Adic.LisseCover.TransitionCocycle
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.LisseLatticeBasis

/-!
# Integral changes of trivialisation on regular schemes

Let `S` be a regular Noetherian scheme, `{f_k : V_k ⟶ S}` a finite pro-étale cover by affine
schemes and `T_{jk}(a, b)(x) ∈ GL_n(E)` a system of transition values: continuous in the point
`x` of a scheme `W` with `a : W ⟶ V_j`, `b : W ⟶ V_k` over `S`, compatible with precomposition
and satisfying the cocycle condition (the values of the transition matrices of a trivialisation,
`AlgebraicGeometry.ProEtale.exists_transitionValues`). Then there are continuous
`g_k : V_k → GL_n(E)` such that the conjugates `g_j(p₁ w)⁻¹ T_{jk}(p₁, p₂)(w) g_k(p₂ w)` on the
fibre products `V_j ×_S V_k` and their inverses have integral entries
(`AlgebraicGeometry.exists_integral_conj_of_transitionValues`).

The proof: on the single cover `F : ∐ V_k ⟶ S`, the transition values define a continuous
cocycle `γ : (∐ V_k) ×_S (∐ V_k) → GL_n(E)`, a point of the fibre product being the image of a
point of a scheme `R` with `a : R ⟶ V_j`, `b : R ⟶ V_k`; it acts on the lattices of `Eⁿ` by a
descent cocycle. By the lattice theorem on regular schemes
(`AlgebraicGeometry.exists_isTwistedSection_compactOpenLattice`, blueprint
`lemma-lattices-after-finite-stratification`), it has a lattice-valued twisted section `σ`; the
bases `g` of the `𝒪_E`-spans of the lattices `σ` (`PadicAlgCl.CompactOpenLattice.integersBasisGL`)
are locally constant and conjugate `γ` into `GL_n(𝒪_E)`
(`PadicAlgCl.CompactOpenLattice.norm_integersBasisGL_inv_mul_mul_le_one`).
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

open PadicAlgCl

variable {l : ℕ} [Fact l.Prime] {E : IntermediateField ℚ_[l] (PadicAlgCl l)}
  [FiniteDimensional ℚ_[l] E]

/-- A point of a scheme mapping to a disjoint union lifts, along a morphism `ρ : R ⟶ X` hitting
the point, to one of the summands. -/
lemma exists_lift_sigmaι {κ : Type u} [Small.{u} κ] (V : κ → Scheme.{u}) {X : Scheme.{u}}
    (x : X ⟶ ∐ V) (w : X) :
    ∃ (j : κ) (R : Scheme.{u}) (ρ : R ⟶ X) (a : R ⟶ V j) (r : R),
      ρ.base r = w ∧ a ≫ Sigma.ι V j = ρ ≫ x := by
  obtain ⟨j, v, hv⟩ := (sigmaOpenCover V).exists_eq (x.base w)
  obtain ⟨r, hr₁, hr₂⟩ := Scheme.Pullback.exists_preimage_pullback (f := Sigma.ι V j) (g := x) v w
    hv
  exact ⟨j, _, pullback.snd _ _, pullback.fst _ _, r, hr₂, pullback.condition⟩

/-- **Integral conjugates of transition values on regular schemes.** See the module docstring. -/
theorem exists_integral_conj_of_transitionValues {S : Scheme.{u}} [IsLocallyNoetherian S]
    [CompactSpace S] [QuasiSeparatedSpace S] [IsRegular S]
    (𝒰 : Scheme.Cover.{u} Scheme.proetalePrecoverage S) [Finite 𝒰.I₀] [∀ k, IsAffine (𝒰.X k)]
    {n : ℕ}
    (Tval : ∀ (j k : 𝒰.I₀) (W : Scheme.{u}) (a : W ⟶ 𝒰.X j) (b : W ⟶ 𝒰.X k),
        a ≫ 𝒰.f j = b ≫ 𝒰.f k → W → GL (Fin n) E)
    (hc : ∀ j k W a b h i i', Continuous fun x ↦
      ((Tval j k W a b h x : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) i i')
    (hc' : ∀ j k W a b h i i', Continuous fun x ↦
      (((Tval j k W a b h x)⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) i i')
    (hcomp : ∀ j k (W W' : Scheme.{u}) (c : W' ⟶ W) a b h h' x,
      Tval j k W' (c ≫ a) (c ≫ b) h' x = Tval j k W a b h (c.base x))
    (htrans : ∀ j k l W a b c h h' h'' x,
      Tval j l W a c h'' x = Tval j k W a b h x * Tval k l W b c h' x)
    (hself : ∀ k W a h x, Tval k k W a a h x = 1) :
    ∃ g : ∀ k, 𝒰.X k → GL (Fin n) E,
      (∀ k i i', Continuous fun v ↦ ((g k v : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) i i') ∧
      (∀ k i i', Continuous fun v ↦
        (((g k v)⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) i i') ∧
      (∀ j k (w : ↥(pullback (𝒰.f j) (𝒰.f k))) i i',
        ‖(((g j ((pullback.fst (𝒰.f j) (𝒰.f k)).base w))⁻¹ *
          Tval j k _ (pullback.fst (𝒰.f j) (𝒰.f k)) (pullback.snd (𝒰.f j) (𝒰.f k))
            pullback.condition w * g k ((pullback.snd (𝒰.f j) (𝒰.f k)).base w) :
              GL (Fin n) E) : Matrix (Fin n) (Fin n) E) i i'‖ ≤ 1) ∧
      (∀ j k (w : ↥(pullback (𝒰.f j) (𝒰.f k))) i i',
        ‖((((g j ((pullback.fst (𝒰.f j) (𝒰.f k)).base w))⁻¹ *
          Tval j k _ (pullback.fst (𝒰.f j) (𝒰.f k)) (pullback.snd (𝒰.f j) (𝒰.f k))
            pullback.condition w * g k ((pullback.snd (𝒰.f j) (𝒰.f k)).base w))⁻¹ :
              GL (Fin n) E) : Matrix (Fin n) (Fin n) E) i i'‖ ≤ 1) := by
  classical
  -- the single cover `F : ∐ V_k ⟶ S`
  let F : ∐ 𝒰.X ⟶ S := Sigma.desc 𝒰.f
  have hιF (k : 𝒰.I₀) : Sigma.ι 𝒰.X k ≫ F = 𝒰.f k := Sigma.ι_comp_desc _ _
  have hwe (k : 𝒰.I₀) : WeaklyEtale (𝒰.f k) :=
    Scheme.proetalePrecoverage_le_precoverage_weaklyEtale _ 𝒰.mem₀ (.mk k)
  have : WeaklyEtale F := IsZariskiLocalAtSource.sigmaDesc (P := @WeaklyEtale) fun k ↦ hwe k
  have : Surjective F := by
    refine ⟨fun s ↦ ?_⟩
    have hsurj := ((Scheme.ofArrows_mem_precoverage_iff (P := @WeaklyEtale)).1
      (Scheme.propQCPrecoverage_le_precoverage _ 𝒰.mem₀)).1 s
    obtain ⟨k, v, hv⟩ := hsurj
    refine ⟨(Sigma.ι 𝒰.X k).base v, ?_⟩
    rw [← Scheme.Hom.comp_apply, hιF, hv]
  have : QuasiCompact F := inferInstance
  -- the charts of the fibre product `(∐ V_k) ×_S (∐ V_k)`
  let chart (j k : 𝒰.I₀) (R : Scheme.{u}) (a : R ⟶ 𝒰.X j) (b : R ⟶ 𝒰.X k)
      (h : a ≫ 𝒰.f j = b ≫ 𝒰.f k) : R ⟶ pullback F F :=
    pullback.lift (a ≫ Sigma.ι 𝒰.X j) (b ≫ Sigma.ι 𝒰.X k) (by
      rw [Category.assoc, Category.assoc, hιF, hιF, h])
  have hchart₁ (j k : 𝒰.I₀) (R : Scheme.{u}) (a : R ⟶ 𝒰.X j) (b : R ⟶ 𝒰.X k)
      (h : a ≫ 𝒰.f j = b ≫ 𝒰.f k) : chart j k R a b h ≫ pullback.fst F F = a ≫ Sigma.ι 𝒰.X j :=
    pullback.lift_fst _ _ _
  have hchart₂ (j k : 𝒰.I₀) (R : Scheme.{u}) (a : R ⟶ 𝒰.X j) (b : R ⟶ 𝒰.X k)
      (h : a ≫ 𝒰.f j = b ≫ 𝒰.f k) : chart j k R a b h ≫ pullback.snd F F = b ≫ Sigma.ι 𝒰.X k :=
    pullback.lift_snd _ _ _
  -- every point of the fibre product is the image of a point of a chart
  have hex (z : ↥(pullback F F)) : ∃ (j k : 𝒰.I₀) (R : Scheme.{u}) (a : R ⟶ 𝒰.X j)
      (b : R ⟶ 𝒰.X k) (h : a ≫ 𝒰.f j = b ≫ 𝒰.f k) (r : R), (chart j k R a b h) r = z := by
    obtain ⟨j, R₁, ρ₁, a₁, r₁, hr₁, ha₁⟩ := exists_lift_sigmaι 𝒰.X (pullback.fst F F) z
    obtain ⟨k, R, ρ₂, b, r, hr, hb⟩ := exists_lift_sigmaι 𝒰.X (ρ₁ ≫ pullback.snd F F) r₁
    have h : (ρ₂ ≫ a₁) ≫ 𝒰.f j = b ≫ 𝒰.f k := by
      rw [← hιF j, ← hιF k, Category.assoc, ← Category.assoc a₁, ha₁, ← Category.assoc b, hb]
      simp only [Category.assoc, pullback.condition]
    refine ⟨j, k, R, ρ₂ ≫ a₁, b, h, r, ?_⟩
    have e : chart j k R (ρ₂ ≫ a₁) b h = ρ₂ ≫ ρ₁ := pullback.hom_ext
      (by rw [hchart₁ j k R _ b h, Category.assoc, ha₁, Category.assoc])
      (by rw [hchart₂ j k R _ b h, hb, Category.assoc])
    rw [e, Scheme.Hom.comp_apply, hr, hr₁]
  -- the values do not depend on the chart
  have hTcongr (j k : 𝒰.I₀) (W : Scheme.{u}) {a a₁ : W ⟶ 𝒰.X j} {b b₁ : W ⟶ 𝒰.X k}
      (ha : a = a₁) (hb : b = b₁) (h : a ≫ 𝒰.f j = b ≫ 𝒰.f k) (h₁ : a₁ ≫ 𝒰.f j = b₁ ≫ 𝒰.f k)
      (x : W) : Tval j k W a b h x = Tval j k W a₁ b₁ h₁ x := by
    subst ha hb
    rfl
  have hcons (j k : 𝒰.I₀) (R : Scheme.{u}) (a : R ⟶ 𝒰.X j) (b : R ⟶ 𝒰.X k)
      (h : a ≫ 𝒰.f j = b ≫ 𝒰.f k) (r : R) (j' k' : 𝒰.I₀) (R' : Scheme.{u}) (a' : R' ⟶ 𝒰.X j')
      (b' : R' ⟶ 𝒰.X k') (h' : a' ≫ 𝒰.f j' = b' ≫ 𝒰.f k') (r' : R')
      (he : (chart j k R a b h) r = (chart j' k' R' a' b' h') r') :
      Tval j k R a b h r = Tval j' k' R' a' b' h' r' := by
    obtain ⟨q, hq₁, hq₂⟩ := Scheme.Pullback.exists_preimage_pullback
      (f := chart j k R a b h) (g := chart j' k' R' a' b' h') r r' he
    have hw := pullback.condition (f := chart j k R a b h) (g := chart j' k' R' a' b' h')
    have hfst : pullback.fst _ _ ≫ a ≫ Sigma.ι 𝒰.X j =
        pullback.snd (chart j k R a b h) (chart j' k' R' a' b' h') ≫ a' ≫ Sigma.ι 𝒰.X j' := by
      rw [← hchart₁ j k R a b h, ← hchart₁ j' k' R' a' b' h', reassoc_of% hw]
    have hsnd : pullback.fst _ _ ≫ b ≫ Sigma.ι 𝒰.X k =
        pullback.snd (chart j k R a b h) (chart j' k' R' a' b' h') ≫ b' ≫ Sigma.ι 𝒰.X k' := by
      rw [← hchart₂ j k R a b h, ← hchart₂ j' k' R' a' b' h', reassoc_of% hw]
    obtain rfl : j = j' := by
      have := congrArg (fun φ ↦ φ.base q) hfst
      simp only [Scheme.Hom.comp_apply] at this
      exact congrArg Sigma.fst ((sigmaι_eq_iff _ _ _ _ _).1 this)
    obtain rfl : k = k' := by
      have := congrArg (fun φ ↦ φ.base q) hsnd
      simp only [Scheme.Hom.comp_apply] at this
      exact congrArg Sigma.fst ((sigmaι_eq_iff _ _ _ _ _).1 this)
    have ha : pullback.fst (chart j k R a b h) (chart j k R' a' b' h') ≫ a =
        pullback.snd (chart j k R a b h) (chart j k R' a' b' h') ≫ a' := by
      rw [← cancel_mono (Sigma.ι 𝒰.X j), Category.assoc, Category.assoc]
      exact hfst
    have hb : pullback.fst (chart j k R a b h) (chart j k R' a' b' h') ≫ b =
        pullback.snd (chart j k R a b h) (chart j k R' a' b' h') ≫ b' := by
      rw [← cancel_mono (Sigma.ι 𝒰.X k), Category.assoc, Category.assoc]
      exact hsnd
    rw [← hq₁, ← hq₂, ← hcomp j k R _ _ a b h (by rw [Category.assoc, h, Category.assoc]),
      ← hcomp j k R' _ _ a' b' h' (by rw [Category.assoc, h', Category.assoc])]
    exact hTcongr j k _ ha hb _ _ q
  -- the cocycle on the fibre product
  choose cj ck cR ca cb ch cr hcr using hex
  let γ : ↥(pullback F F) → GL (Fin n) E := fun z ↦
    Tval (cj z) (ck z) (cR z) (ca z) (cb z) (ch z) (cr z)
  have hγ (j k : 𝒰.I₀) (R : Scheme.{u}) (a : R ⟶ 𝒰.X j) (b : R ⟶ 𝒰.X k)
      (h : a ≫ 𝒰.f j = b ≫ 𝒰.f k) (r : R) : γ ((chart j k R a b h) r) = Tval j k R a b h r :=
    hcons _ _ _ _ _ _ _ _ _ _ _ _ _ _ (hcr _)
  -- the charts of the fibre products `V_j ×_S V_k` are open immersions covering
  have hopen (j k : 𝒰.I₀) : IsOpenImmersion (chart j k _ (pullback.fst (𝒰.f j) (𝒰.f k))
      (pullback.snd (𝒰.f j) (𝒰.f k)) pullback.condition) := by
    have e : chart j k _ (pullback.fst (𝒰.f j) (𝒰.f k)) (pullback.snd (𝒰.f j) (𝒰.f k))
        pullback.condition = pullback.map (𝒰.f j) (𝒰.f k) F F (Sigma.ι 𝒰.X j) (Sigma.ι 𝒰.X k)
          (𝟙 S) (by rw [hιF, Category.comp_id]) (by rw [hιF, Category.comp_id]) :=
      pullback.hom_ext (by simp [hchart₁]) (by simp [hchart₂])
    rw [e]
    infer_instance
  have hcover (z : ↥(pullback F F)) : ∃ (j k : 𝒰.I₀) (w : ↥(pullback (𝒰.f j) (𝒰.f k))),
      (chart j k _ (pullback.fst (𝒰.f j) (𝒰.f k)) (pullback.snd (𝒰.f j) (𝒰.f k))
        pullback.condition) w = z := by
    refine ⟨cj z, ck z, (pullback.lift (ca z) (cb z) (ch z)) (cr z), ?_⟩
    have e : pullback.lift (ca z) (cb z) (ch z) ≫ chart (cj z) (ck z) _
        (pullback.fst (𝒰.f (cj z)) (𝒰.f (ck z))) (pullback.snd (𝒰.f (cj z)) (𝒰.f (ck z)))
          pullback.condition = chart (cj z) (ck z) (cR z) (ca z) (cb z) (ch z) :=
      pullback.hom_ext (by rw [Category.assoc, hchart₁ _ _ _ _ _ pullback.condition,
          pullback.lift_fst_assoc, hchart₁ _ _ _ _ _ (ch z)])
        (by rw [Category.assoc, hchart₂ _ _ _ _ _ pullback.condition, pullback.lift_snd_assoc,
          hchart₂ _ _ _ _ _ (ch z)])
    rw [← Scheme.Hom.comp_apply, e, hcr]
  have hγc (i i' : Fin n) :
      Continuous fun z ↦ ((γ z : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) i i' := by
    refine continuous_iff_continuousAt.2 fun z ↦ ?_
    obtain ⟨j, k, w, rfl⟩ := hcover z
    have := hopen j k
    refine (Scheme.Hom.isOpenEmbedding (chart j k _ (pullback.fst (𝒰.f j) (𝒰.f k))
      (pullback.snd (𝒰.f j) (𝒰.f k)) pullback.condition)).continuousAt_iff.1 ?_
    have e : (fun z ↦ ((γ z : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) i i') ∘
        (chart j k _ (pullback.fst (𝒰.f j) (𝒰.f k)) (pullback.snd (𝒰.f j) (𝒰.f k))
          pullback.condition) = fun w ↦
        ((Tval j k _ (pullback.fst (𝒰.f j) (𝒰.f k)) (pullback.snd (𝒰.f j) (𝒰.f k))
          pullback.condition w : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) i i' :=
      funext fun w ↦ by rw [Function.comp_apply, hγ]
    rw [e]
    exact (hc j k _ _ _ _ i i').continuousAt
  have hγc' (i i' : Fin n) :
      Continuous fun z ↦ (((γ z)⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) i i' := by
    refine continuous_iff_continuousAt.2 fun z ↦ ?_
    obtain ⟨j, k, w, rfl⟩ := hcover z
    have := hopen j k
    refine (Scheme.Hom.isOpenEmbedding (chart j k _ (pullback.fst (𝒰.f j) (𝒰.f k))
      (pullback.snd (𝒰.f j) (𝒰.f k)) pullback.condition)).continuousAt_iff.1 ?_
    have e : (fun z ↦ (((γ z)⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) i i') ∘
        (chart j k _ (pullback.fst (𝒰.f j) (𝒰.f k)) (pullback.snd (𝒰.f j) (𝒰.f k))
          pullback.condition) = fun w ↦
        (((Tval j k _ (pullback.fst (𝒰.f j) (𝒰.f k)) (pullback.snd (𝒰.f j) (𝒰.f k))
          pullback.condition w)⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) i i' :=
      funext fun w ↦ by rw [Function.comp_apply, hγ]
    rw [e]
    exact (hc' j k _ _ _ _ i i').continuousAt
  -- the cocycle is trivial on the diagonal
  have hdiag (v : ↥(∐ 𝒰.X)) : γ ((pullback.diagonal F) v) = 1 := by
    obtain ⟨j, R, ρ, a, r, rfl, ha⟩ := exists_lift_sigmaι 𝒰.X (𝟙 _) v
    rw [Category.comp_id] at ha
    have e : ρ ≫ pullback.diagonal F = chart j j R a a rfl :=
      pullback.hom_ext (by rw [Category.assoc, pullback.diagonal_fst, Category.comp_id,
          hchart₁ j j R a a rfl, ha])
        (by rw [Category.assoc, pullback.diagonal_snd, Category.comp_id,
          hchart₂ j j R a a rfl, ha])
    rw [← Scheme.Hom.comp_apply, e, hγ j j R a a rfl, hself j R a rfl]
  -- the cocycle condition
  have hcoc (w : ↥(tripleProduct F)) : γ ((tripleProj₁₃ F) w) =
      γ ((pullback.fst (pullback.snd F F) (pullback.fst F F)) w) *
        γ ((pullback.snd (pullback.snd F F) (pullback.fst F F)) w) := by
    have hq : pullback.fst (pullback.snd F F) (pullback.fst F F) ≫ pullback.snd F F =
        pullback.snd (pullback.snd F F) (pullback.fst F F) ≫ pullback.fst F F :=
      pullback.condition
    obtain ⟨j₁, R₁, ρ₁, a₁, r₁, rfl, ha₁⟩ := exists_lift_sigmaι 𝒰.X
      (pullback.fst (pullback.snd F F) (pullback.fst F F) ≫ pullback.fst F F) w
    obtain ⟨j₂, R₂, ρ₂, a₂, r₂, rfl, ha₂⟩ := exists_lift_sigmaι 𝒰.X
      (ρ₁ ≫ pullback.fst (pullback.snd F F) (pullback.fst F F) ≫ pullback.snd F F) r₁
    obtain ⟨j₃, R₃, ρ₃, a₃, r₃, rfl, ha₃⟩ := exists_lift_sigmaι 𝒰.X
      (ρ₂ ≫ ρ₁ ≫ pullback.snd (pullback.snd F F) (pullback.fst F F) ≫ pullback.snd F F) r₂
    obtain ⟨ρ, hρ⟩ : ∃ ρ, ρ = ρ₃ ≫ ρ₂ ≫ ρ₁ := ⟨_, rfl⟩
    obtain ⟨b₁, hb₁'⟩ : ∃ b₁, b₁ = ρ₃ ≫ ρ₂ ≫ a₁ := ⟨_, rfl⟩
    obtain ⟨b₂, hb₂'⟩ : ∃ b₂, b₂ = ρ₃ ≫ a₂ := ⟨_, rfl⟩
    have hb₁ : b₁ ≫ Sigma.ι 𝒰.X j₁ =
        ρ ≫ pullback.fst (pullback.snd F F) (pullback.fst F F) ≫ pullback.fst F F := by
      rw [hb₁', hρ, Category.assoc, Category.assoc, ha₁, Category.assoc, Category.assoc]
    have hb₂ : b₂ ≫ Sigma.ι 𝒰.X j₂ =
        ρ ≫ pullback.fst (pullback.snd F F) (pullback.fst F F) ≫ pullback.snd F F := by
      rw [hb₂', hρ, Category.assoc, ha₂, Category.assoc, Category.assoc]
    have hb₂'' : b₂ ≫ Sigma.ι 𝒰.X j₂ =
        ρ ≫ pullback.snd (pullback.snd F F) (pullback.fst F F) ≫ pullback.fst F F := by
      rw [hb₂, hq]
    have hb₃ : a₃ ≫ Sigma.ι 𝒰.X j₃ =
        ρ ≫ pullback.snd (pullback.snd F F) (pullback.fst F F) ≫ pullback.snd F F := by
      simp only [ha₃, hρ, Category.assoc]
    have hF₁ : b₁ ≫ 𝒰.f j₁ =
        ρ ≫ pullback.fst (pullback.snd F F) (pullback.fst F F) ≫ pullback.fst F F ≫ F := by
      rw [← hιF, ← Category.assoc, hb₁, Category.assoc, Category.assoc]
    have hF₂ : b₂ ≫ 𝒰.f j₂ =
        ρ ≫ pullback.fst (pullback.snd F F) (pullback.fst F F) ≫ pullback.fst F F ≫ F := by
      rw [← hιF, ← Category.assoc, hb₂, Category.assoc, Category.assoc,
        pullback.condition (f := F) (g := F)]
    have hF₃ : a₃ ≫ 𝒰.f j₃ =
        ρ ≫ pullback.fst (pullback.snd F F) (pullback.fst F F) ≫ pullback.fst F F ≫ F := by
      rw [← hιF, ← Category.assoc, hb₃, Category.assoc, Category.assoc,
        ← pullback.condition (f := F) (g := F), ← reassoc_of% hq,
        pullback.condition (f := F) (g := F)]
    have h₁₂ : b₁ ≫ 𝒰.f j₁ = b₂ ≫ 𝒰.f j₂ := hF₁.trans hF₂.symm
    have h₂₃ : b₂ ≫ 𝒰.f j₂ = a₃ ≫ 𝒰.f j₃ := hF₂.trans hF₃.symm
    have h₁₃ : b₁ ≫ 𝒰.f j₁ = a₃ ≫ 𝒰.f j₃ := hF₁.trans hF₃.symm
    have e₁₂ : ρ ≫ pullback.fst (pullback.snd F F) (pullback.fst F F) =
        chart j₁ j₂ R₃ b₁ b₂ h₁₂ :=
      pullback.hom_ext (by rw [hchart₁ _ _ _ _ _ h₁₂, hb₁, Category.assoc])
        (by rw [hchart₂ _ _ _ _ _ h₁₂, hb₂, Category.assoc])
    have e₂₃ : ρ ≫ pullback.snd (pullback.snd F F) (pullback.fst F F) =
        chart j₂ j₃ R₃ b₂ a₃ h₂₃ :=
      pullback.hom_ext (by rw [hchart₁ _ _ _ _ _ h₂₃, hb₂'', Category.assoc])
        (by rw [hchart₂ _ _ _ _ _ h₂₃, hb₃, Category.assoc])
    have e₁₃ : ρ ≫ tripleProj₁₃ F = chart j₁ j₃ R₃ b₁ a₃ h₁₃ :=
      pullback.hom_ext
        (by rw [hchart₁ _ _ _ _ _ h₁₃, hb₁, Category.assoc, tripleProj₁₃, pullback.lift_fst])
        (by rw [hchart₂ _ _ _ _ _ h₁₃, hb₃, Category.assoc, tripleProj₁₃, pullback.lift_snd])
    have hw : ρ₁.base (ρ₂.base (ρ₃.base r₃)) = ρ r₃ := by
      rw [hρ, Scheme.Hom.comp_apply, Scheme.Hom.comp_apply]
    rw [hw, ← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, e₁₂, e₂₃,
      e₁₃, hγ, hγ, hγ]
    exact htrans j₁ j₂ j₃ R₃ b₁ b₂ a₃ h₁₂ h₂₃ h₁₃ r₃
  -- the lattice theorem
  have hdc := ProEtale.AdicSheaf.isDescentCocycle_smul_compactOpenLattice F γ hγc hγc'
    (fun v ↦ hdiag v) (fun w ↦ hcoc w)
  obtain ⟨σ, hσlc, hσ⟩ := exists_isTwistedSection_compactOpenLattice F γ hdc
  let s : ∐ 𝒰.X ⟶ pullback F (𝟙 S) :=
    pullback.lift (𝟙 _) F (by rw [Category.id_comp, Category.comp_id])
  have hlc (k : 𝒰.I₀) : IsLocallyConstant fun v ↦
      CompactOpenLattice.integersBasisGL (σ ((Sigma.ι 𝒰.X k ≫ s) v)) :=
    (hσlc.comp_continuous (Sigma.ι 𝒰.X k ≫ s).continuous).comp
      CompactOpenLattice.integersBasisGL
  have hkey (j k : 𝒰.I₀) (w : ↥(pullback (𝒰.f j) (𝒰.f k))) :
      σ ((Sigma.ι 𝒰.X j ≫ s) ((pullback.fst (𝒰.f j) (𝒰.f k)) w)) =
        Tval j k _ (pullback.fst (𝒰.f j) (𝒰.f k)) (pullback.snd (𝒰.f j) (𝒰.f k))
          pullback.condition w • σ ((Sigma.ι 𝒰.X k ≫ s) ((pullback.snd (𝒰.f j) (𝒰.f k)) w)) := by
    let μ : pullback (𝒰.f j) (𝒰.f k) ⟶
        pullback (pullback.snd F (𝟙 S)) (pullback.snd F (𝟙 S)) :=
      pullback.lift (pullback.fst (𝒰.f j) (𝒰.f k) ≫ Sigma.ι 𝒰.X j ≫ s)
        (pullback.snd (𝒰.f j) (𝒰.f k) ≫ Sigma.ι 𝒰.X k ≫ s) (by
          simp only [Category.assoc, s, pullback.lift_snd, hιF, pullback.condition])
    have e₁ : μ ≫ pullback.fst (pullback.snd F (𝟙 S)) (pullback.snd F (𝟙 S)) =
        pullback.fst (𝒰.f j) (𝒰.f k) ≫ Sigma.ι 𝒰.X j ≫ s := pullback.lift_fst _ _ _
    have e₂ : μ ≫ pullback.snd (pullback.snd F (𝟙 S)) (pullback.snd F (𝟙 S)) =
        pullback.snd (𝒰.f j) (𝒰.f k) ≫ Sigma.ι 𝒰.X k ≫ s := pullback.lift_snd _ _ _
    have e₃ : μ ≫ twistedPairMap F (𝟙 S) = chart j k _ (pullback.fst (𝒰.f j) (𝒰.f k))
        (pullback.snd (𝒰.f j) (𝒰.f k)) pullback.condition :=
      pullback.hom_ext
        (by
          rw [hchart₁ _ _ _ _ _ pullback.condition, Category.assoc, twistedPairMap,
            pullback.lift_fst, reassoc_of% e₁]
          simp [s])
        (by
          rw [hchart₂ _ _ _ _ _ pullback.condition, Category.assoc, twistedPairMap,
            pullback.lift_snd, reassoc_of% e₂]
          simp [s])
    have h := hσ (μ w)
    rw [← Scheme.Hom.comp_apply, e₁, ← Scheme.Hom.comp_apply, e₃, ← Scheme.Hom.comp_apply, e₂] at h
    beta_reduce at h
    rw [hγ j k _ _ _ pullback.condition, Scheme.Hom.comp_apply, Scheme.Hom.comp_apply] at h
    exact h
  refine ⟨fun k v ↦ CompactOpenLattice.integersBasisGL (σ ((Sigma.ι 𝒰.X k ≫ s) v)),
    fun k i i' ↦ ((hlc k).comp fun A ↦ (A : Matrix (Fin n) (Fin n) E) i i').continuous,
    fun k i i' ↦ ((hlc k).comp fun A ↦ ((A⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) i i'
      ).continuous, fun j k w i i' ↦ ?_, fun j k w i i' ↦ ?_⟩
  · exact CompactOpenLattice.norm_integersBasisGL_inv_mul_mul_le_one _ (hkey j k w).symm i i'
  · rw [mul_inv_rev, mul_inv_rev, inv_inv, ← _root_.mul_assoc]
    exact CompactOpenLattice.norm_integersBasisGL_inv_mul_mul_le_one _
      (inv_smul_eq_iff.2 (hkey j k w)) i i'

end AlgebraicGeometry
