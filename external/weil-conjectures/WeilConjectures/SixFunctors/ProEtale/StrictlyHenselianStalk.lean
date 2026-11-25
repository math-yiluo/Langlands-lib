/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Sites.StrictlyHenselianWeaklyEtale
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Germ

/-!
# Pro-étale sections over a strictly henselian local scheme

Let `A` be a strictly henselian local ring and `c : Spec K ⟶ Spec A` a geometric point over the
closed point, `K` algebraically closed. For every sheaf `P` of modules on the small pro-étale
site of `Spec A`, the restriction `Γ(Spec A, P) ⟶ P_c = Γ(Spec K, c^* P)` of global sections to
the stalk at `c` is bijective
(`AlgebraicGeometry.ProEtale.bijective_germ_of_isStrictlyHenselianLocalRing`).

Indeed every element of the stalk is the germ of a section over a pro-étale neighbourhood
`(V, t)` of `c` (`AlgebraicGeometry.ProEtale.exists_germ_eq`), and the weakly étale
`V ⟶ Spec A` has a section through `t`
(`AlgebraicGeometry.Scheme.exists_section_comp_eq_of_weaklyEtale`, by Olivier's theorem), along
which the section of `P` restricts to a global section with the same germ. Similarly a global
section with vanishing germ vanishes on a neighbourhood
(`AlgebraicGeometry.ProEtale.exists_map_eq_zero_of_germ_eq_zero`), which has a section, hence
vanishes.
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry.ProEtale

open Scheme

set_option backward.isDefEq.respectTransparency.types false

variable {A : Type u} [CommRing A] [IsStrictlyHenselianLocalRing A] {K : Type u} [Field K]

/-- The lift `Spec K ⟶ Spec A ×_{Spec A} Spec K` of a morphism `c : Spec K ⟶ Spec A` to the
base change along `c` of the terminal object of the pro-étale site of `Spec A`: the point at
which germs of global sections are taken. -/
noncomputable def terminalPoint (c : Spec (.of K) ⟶ Spec (.of A)) :
    ProEt.mk (𝟙 (Spec (.of K))) ⟶
      (MorphismProperty.Over.pullback @WeaklyEtale ⊤ c).obj (ProEt.mk (𝟙 (Spec (.of A)))) :=
  MorphismProperty.Over.homMk (pullback.lift c (𝟙 _) (Category.comp_id c))
    (by exact pullback.lift_snd _ _ _)

variable {R : Type (u + 1)} [Ring R] (c : Spec (.of K) ⟶ Spec (.of A))
  (P : Sheaf (ProEt.topology (Spec (.of A))) (ModuleCat.{u + 1} R))

/-- A morphism `ProEt.mk (𝟙 _) ⟶ V` in the pro-étale site of `Spec A` from a section of the
structure morphism of `V`. -/
noncomputable def homOfSection {V : (Spec (.of A)).ProEt} (s : Spec (.of A) ⟶ V.left)
    (hs : s ≫ V.hom = 𝟙 _) : ProEt.mk (𝟙 (Spec (.of A))) ⟶ V :=
  MorphismProperty.Over.homMk s hs

/-- Every pro-étale neighbourhood `(V, t)` of the geometric point `c` over the closed point of
the strictly henselian `Spec A` receives a morphism from the terminal neighbourhood. -/
lemma exists_homOfSection (hc : c (IsLocalRing.closedPoint K) = IsLocalRing.closedPoint A)
    {V : (Spec (.of A)).ProEt}
    (t : ProEt.mk (𝟙 (Spec (.of K))) ⟶ (MorphismProperty.Over.pullback @WeaklyEtale ⊤ c).obj V) :
    ∃ f : ProEt.mk (𝟙 (Spec (.of A))) ⟶ V,
      terminalPoint c ≫ (MorphismProperty.Over.pullback @WeaklyEtale ⊤ c).map f = t := by
  have ht : t.left ≫ pullback.snd V.hom c = 𝟙 (Spec (.of K)) := MorphismProperty.Over.w t
  obtain ⟨s, hs, hcs⟩ := exists_section_comp_eq_of_weaklyEtale V.hom c hc
    (t.left ≫ pullback.fst V.hom c) (by
      rw [Category.assoc, pullback.condition, ← Category.assoc, ht, Category.id_comp])
  refine ⟨homOfSection s hs, MorphismProperty.Over.Hom.ext ?_⟩
  apply pullback.hom_ext
  · change (pullback.lift c (𝟙 _) (Category.comp_id c) ≫
      pullback.lift (pullback.fst (𝟙 _) c ≫ s) (pullback.snd (𝟙 _) c) _) ≫
        pullback.fst V.hom c = _
    rw [Category.assoc, pullback.lift_fst, pullback.lift_fst_assoc, hcs]
  · change (pullback.lift c (𝟙 _) (Category.comp_id c) ≫
      pullback.lift (pullback.fst (𝟙 _) c ≫ s) (pullback.snd (𝟙 _) c) _) ≫
        pullback.snd V.hom c = _
    rw [Category.assoc, pullback.lift_snd, pullback.lift_snd, ht]

/-- **Global sections over a strictly henselian local scheme are the stalk at the closed
point.** For a strictly henselian local ring `A`, a geometric point `c : Spec K ⟶ Spec A` over
the closed point and a sheaf of modules `P` on `(Spec A)_proét`, the germ map
`Γ(Spec A, P) ⟶ Γ(Spec K, c^* P)` is bijective. -/
theorem bijective_germ_of_isStrictlyHenselianLocalRing [IsAlgClosed K]
    (hc : c (IsLocalRing.closedPoint K) = IsLocalRing.closedPoint A) :
    Function.Bijective (germ _ c P (terminalPoint c)) := by
  refine ⟨(injective_iff_map_eq_zero _).2 fun σ hσ ↦ ?_, fun a ↦ ?_⟩
  · obtain ⟨V', f, t', -, hf⟩ := exists_map_eq_zero_of_germ_eq_zero c P (terminalPoint c) σ hσ
    obtain ⟨ψ, -⟩ := exists_homOfSection c hc t'
    have hψ : ψ ≫ f = 𝟙 _ := (ProEt.isTerminalMkId _).hom_ext _ _
    have h := congrArg (fun φ ↦ P.obj.map φ.op σ) hψ
    simp only [op_comp, Functor.map_comp, op_id] at h
    rw [ConcreteCategory.comp_apply, hf, map_zero] at h
    simpa using h.symm
  · obtain ⟨V, t, σ, rfl⟩ := exists_germ_eq c P a
    obtain ⟨f, hf⟩ := exists_homOfSection c hc t
    refine ⟨P.obj.map f.op σ, ?_⟩
    rw [← ConcreteCategory.comp_apply, map_germ f t (terminalPoint c) hf]

end AlgebraicGeometry.ProEtale
