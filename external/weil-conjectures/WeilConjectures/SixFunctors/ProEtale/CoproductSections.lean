/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Sites.DisjointGluing
public import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Proetale

/-!
# Sections of pro-étale sheaves over finite disjoint unions

Let `fᵢ : Tᵢ ⟶ W` be a finite family of morphisms of the small pro-étale site of `X` whose
underlying morphisms of schemes exhibit `W` as the disjoint union `∐ᵢ Tᵢ`. Then the sections of
any pro-étale sheaf over `W` are the product of its sections over the `Tᵢ`
(`AlgebraicGeometry.ProEtale.isLimitSectionsFanOfIsColimitCofan`): the `fᵢ` form a disjoint
Zariski covering family, so the sheaf condition for it imposes no compatibility condition.
-/

@[expose] public section

universe w u' u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry

open Scheme

variable {X W : Scheme.{u}} {ι : Type u} {T : ι → Scheme.{u}} {f : ∀ i, T i ⟶ W}

/-- The legs of a finite coproduct cofan of schemes are open immersions. -/
lemma Scheme.isOpenImmersion_of_isColimit_cofan (hf : IsColimit (Cofan.mk W f)) (i : ι) :
    IsOpenImmersion (f i) := by
  have e : f i = Sigma.ι T i ≫ (hf.coconePointUniqueUpToIso (coproductIsCoproduct T)).inv :=
    (IsColimit.comp_coconePointUniqueUpToIso_inv hf (coproductIsCoproduct T) ⟨i⟩).symm
  rw [e]
  infer_instance

/-- The legs of a finite coproduct cofan of schemes are jointly surjective. -/
lemma Scheme.exists_mem_range_of_isColimit_cofan (hf : IsColimit (Cofan.mk W f)) (x : W) :
    ∃ i, x ∈ Set.range (f i) := by
  have : IsIso (Sigma.desc f) := (Cofan.nonempty_isColimit_iff_isIso_sigmaDesc _).mp ⟨hf⟩
  obtain ⟨y, rfl⟩ := (Sigma.desc f).surjective x
  obtain ⟨⟨i, t⟩, rfl⟩ := (sigmaMk T).surjective y
  exact ⟨i, t, by simp [sigmaMk_mk, ← Scheme.Hom.comp_apply]⟩

/-- A scheme mapping compatibly to two distinct legs of a finite coproduct cofan is empty. -/
lemma Scheme.isEmpty_of_isColimit_cofan [Finite ι] (hf : IsColimit (Cofan.mk W f)) {i j : ι}
    (hij : i ≠ j)
    {Z : Scheme.{u}} (a : Z ⟶ T i) (b : Z ⟶ T j) (h : a ≫ f i = b ≫ f j) :
    IsEmpty Z := by
  have hpb := FinitaryExtensive.isPullback_initial_to hf ⟨i⟩ ⟨j⟩ (by simpa using hij)
  have : IsEmpty (⊥_ Scheme.{u}) := isInitial_iff_isEmpty.mp ⟨initialIsInitial⟩
  exact (hpb.lift a b h).base.hom.1.isEmpty

variable {A : Type u'} [Category.{w} A]

/-- **Sections over a finite disjoint union.** If morphisms `fᵢ : Tᵢ ⟶ W` of the small
pro-étale site of `X` exhibit `W` as the disjoint union of the `Tᵢ` on underlying schemes, the
sections of a pro-étale sheaf over `W` are the product of its sections over the `Tᵢ`, with the
restriction maps as projections. -/
noncomputable def ProEtale.isLimitSectionsFanOfIsColimitCofan (G : Sheaf (ProEt.topology X) A)
    [Finite ι] {W : X.ProEt} {T : ι → X.ProEt} (f : ∀ i, T i ⟶ W)
    (hf : IsColimit (Cofan.mk W.left fun i ↦ (f i).left)) :
    IsLimit (Fan.mk (G.obj.obj (op W)) fun i ↦ G.obj.map (f i).op) := by
  have hdisj : Presieve.IsDisjointFamily f (ProEt.topology X) :=
    { mono i := ⟨fun {Z} a b h ↦ MorphismProperty.Over.Hom.ext <| by
        have : Mono (f i).left := FinitaryExtensive.mono_ι hf ⟨i⟩
        exact (cancel_mono (f i).left).1 (congrArg (fun m ↦ m.left) h)⟩
      bot_mem i j hij Z a b h := by
        have := Scheme.isEmpty_of_isColimit_cofan hf hij a.left b.left
          (congrArg (fun m ↦ m.left) h)
        exact ProEt.bot_mem_topology Z }
  have hcov : Sieve.ofArrows T f ∈ ProEt.topology X W := by
    rw [ProEt.mem_topology_iff]
    refine ⟨Presieve.ofArrows T f, ?_, Sieve.le_generate _⟩
    rw [ProEt.mem_precoverage_iff, Presieve.map_ofArrows]
    exact Scheme.zariskiPrecoverage_le_proetalePrecoverage _
      ((Scheme.ofArrows_mem_precoverage_iff _).mpr
        ⟨Scheme.exists_mem_range_of_isColimit_cofan hf,
          Scheme.isOpenImmersion_of_isColimit_cofan hf⟩)
  have hsh (E : A) (x : ∀ i, E ⟶ G.obj.obj (op (T i))) :
      ∃! t : E ⟶ G.obj.obj (op W), ∀ i, t ≫ G.obj.map (f i).op = x i := by
    have h := G.property E
    have h' := h _ hcov
    rw [← Presieve.isSheafFor_iff_generate, Presieve.isSheafFor_arrows_iff] at h'
    exact h' x (hdisj.compatible ((isSheaf_iff_isSheaf_of_type _ _).2 h) x)
  refine Fan.IsLimit.mk _ (fun s ↦ (hsh s.pt s.proj).choose)
    (fun s i ↦ (hsh s.pt s.proj).choose_spec.1 i)
    (fun s m hm ↦ (hsh s.pt s.proj).choose_spec.2 m hm)

end AlgebraicGeometry
