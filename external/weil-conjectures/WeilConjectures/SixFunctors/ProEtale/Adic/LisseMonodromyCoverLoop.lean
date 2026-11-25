/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.Adic.LisseMonodromyCoverDescent
public import WeilConjectures.SixFunctors.ProEtale.Adic.LisseCover.TwistedSection

/-!
# The loop cocycle of a universal cover

Let `p : Ỹ_t ⟶ Y` be the universal cover at a geometric point `t`. Every point `q` of
`Ỹ_t ×_Y Ỹ_t` lies on the graph `x ↦ (x, g x)` of the transport along a unique loop
`g = U.loop t q ∈ π₁(Y, t)`, which depends continuously on `q`
(`AlgebraicGeometry.Scheme.UniversalCovers.loop`). The loops form a cocycle: the loop of the
diagonal point of `x` is trivial (`AlgebraicGeometry.Scheme.UniversalCovers.loop_diagonal`), and
on `Ỹ_t ×_Y Ỹ_t ×_Y Ỹ_t` the loop of `(y₁, y₃)` is the product of the loops of `(y₂, y₃)` and
`(y₁, y₂)` (`AlgebraicGeometry.Scheme.UniversalCovers.loop_tripleProj₁₃`). Composing with a
representation of `π₁(Y, t)` gives the descent data of the lisse sheaf attached to the
representation.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.Scheme.UniversalCovers

open FiniteEtale

variable {Y : Scheme.{u}} {Ω : Type u} [Field Ω] {U : Scheme.UniversalCovers Y Ω}
  (t : Spec (.of (AlgebraicClosure Ω)) ⟶ Y)

/-- The loop of a point `(x, g x)` is `g`. -/
lemma loop_graph_apply (g : Aut (fiber t)) (x : U.cover t) :
    U.loop t ((graph (U := U) t g).base x) = g :=
  U.loop_graph t g x

/-- The loop is constant along a morphism factoring through the graph of a loop. -/
lemma loop_apply_of_eq_comp {T : Scheme.{u}} (c : T ⟶ pullback (U.proj t) (U.proj t))
    (h : T ⟶ U.cover t) (g : Aut (fiber t)) (hc : c = h ≫ graph (U := U) t g) (x : T) :
    U.loop t (c.base x) = g := by
  rw [hc, Scheme.Hom.comp_apply, loop_graph_apply]

/-- Every point of `Ỹ_t ×_Y Ỹ_t` lies on the graph of its loop. -/
lemma exists_graph_loop (q : (pullback (U.proj t) (U.proj t) : Scheme.{u})) :
    ∃ x : U.cover t, (graph (U := U) t (U.loop t q)).base x = q := by
  obtain ⟨g, x, hx⟩ := U.exists_graph t q
  have hg : U.loop t q = g := by
    rw [← hx]
    exact loop_graph_apply t g x
  exact ⟨x, by rw [hg]; exact hx⟩

/-- The graph of the trivial loop is the diagonal. -/
lemma graph_one : graph (U := U) t 1 = pullback.diagonal (U.proj t) := by
  have h : (U.transport (1 : Aut (fiber t)).asIso).hom = 𝟙 _ := by
    rw [Aut.one_asIso, U.transport_refl]
    rfl
  refine pullback.hom_ext ?_ ?_
  · rw [graph_fst, pullback.diagonal_fst]
  · rw [graph_snd, pullback.diagonal_snd, h]

/-- **The loop of a diagonal point is trivial.** -/
lemma loop_diagonal (x : U.cover t) : U.loop t ((pullback.diagonal (U.proj t)).base x) = 1 := by
  rw [← graph_one, loop_graph_apply]

/-- The graphs of the transports along `g` and `h` compose to the graph of the transport along
`h * g`. -/
lemma transport_mul_hom (g h : Aut (fiber t)) :
    (U.transport (h * g).asIso).hom = (U.transport g.asIso).hom ≫ (U.transport h.asIso).hom := by
  rw [Aut.mul_asIso, U.transport_trans]
  rfl

/-- The first projection `(Ỹ ×_Y Ỹ) ×_Ỹ (Ỹ ×_Y Ỹ) ⟶ Ỹ ×_Y Ỹ` of the triple product. -/
local notation "q₁₂" => pullback.fst (pullback.snd (U.proj t) (U.proj t))
  (pullback.fst (U.proj t) (U.proj t))

/-- The second projection `(Ỹ ×_Y Ỹ) ×_Ỹ (Ỹ ×_Y Ỹ) ⟶ Ỹ ×_Y Ỹ` of the triple product. -/
local notation "q₂₃" => pullback.snd (pullback.snd (U.proj t) (U.proj t))
  (pullback.fst (U.proj t) (U.proj t))

/-- **The loops form a cocycle**: on `Ỹ_t ×_Y Ỹ_t ×_Y Ỹ_t`, the loop of `(y₁, y₃)` is the
product of the loops of `(y₂, y₃)` and of `(y₁, y₂)`. -/
lemma loop_tripleProj₁₃ (τ : tripleProduct (U.proj t)) :
    U.loop t ((tripleProj₁₃ (U.proj t)).base τ) =
      U.loop t ((q₂₃).base τ) * U.loop t ((q₁₂).base τ) := by
  set g := U.loop t ((q₁₂).base τ)
  set h := U.loop t ((q₂₃).base τ)
  -- the first coordinate of `τ` lies on the graph of `g`
  obtain ⟨x, hx⟩ := exists_graph_loop t ((q₁₂).base τ)
  obtain ⟨ρ₁, hρ₁, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := q₁₂)
    (g := graph (U := U) t g) τ x hx.symm
  have hgs : graph (U := U) t g ≫ pullback.snd (U.proj t) (U.proj t) = (U.transport g.asIso).hom :=
    graph_snd t g
  let m₁ : pullback ((U.transport g.asIso).hom) (pullback.fst (U.proj t) (U.proj t)) ⟶
      tripleProduct (U.proj t) :=
    pullback.map _ _ _ _ (graph (U := U) t g) (𝟙 _) (𝟙 _) (by rw [Category.comp_id, hgs])
      (by simp)
  have c₁ := pullback.condition (f := q₁₂) (g := graph (U := U) t g)
  let L₁ : pullback q₁₂ (graph (U := U) t g) ⟶
      pullback ((U.transport g.asIso).hom) (pullback.fst (U.proj t) (U.proj t)) :=
    pullback.lift (pullback.snd _ _) (pullback.fst _ _ ≫ q₂₃) (by
      simp only [Category.assoc]
      rw [← hgs, ← reassoc_of% c₁, pullback.condition (f := pullback.snd (U.proj t) (U.proj t))
        (g := pullback.fst (U.proj t) (U.proj t))])
  have hL₁ : L₁ ≫ m₁ = pullback.fst _ _ := by
    refine pullback.hom_ext ?_ ?_
    · simp only [m₁, L₁, Category.assoc, pullback.lift_fst, pullback.lift_fst_assoc]
      exact c₁.symm
    · simp [m₁, L₁]
  set w := L₁.base ρ₁
  have hτ : m₁.base w = τ := by rw [← Scheme.Hom.comp_apply, hL₁, hρ₁]
  -- the second coordinate lies on the graph of `h`
  have hsw :
      (pullback.snd ((U.transport g.asIso).hom) (pullback.fst (U.proj t) (U.proj t))).base w =
        (q₂₃).base τ := by
    have e := congrArg (q₂₃).base hτ
    rw [← Scheme.Hom.comp_apply, pullback.lift_snd, Category.comp_id] at e
    exact e
  obtain ⟨x', hx'⟩ := exists_graph_loop t
    ((pullback.snd ((U.transport g.asIso).hom) (pullback.fst (U.proj t) (U.proj t))).base w)
  rw [hsw] at hx'
  obtain ⟨ρ₂, hρ₂, -⟩ := Scheme.Pullback.exists_preimage_pullback
    (f := pullback.snd ((U.transport g.asIso).hom) (pullback.fst (U.proj t) (U.proj t)))
    (g := graph (U := U) t h) w x' (hx'.trans hsw.symm).symm
  have hhf : graph (U := U) t h ≫ pullback.fst (U.proj t) (U.proj t) = 𝟙 _ := graph_fst t h
  let m₂ : pullback ((U.transport g.asIso).hom) (𝟙 (U.cover t)) ⟶
      pullback ((U.transport g.asIso).hom) (pullback.fst (U.proj t) (U.proj t)) :=
    pullback.map _ _ _ _ (𝟙 _) (graph (U := U) t h) (𝟙 _) (by simp)
      (by rw [Category.comp_id, hhf])
  have c₂ := pullback.condition
    (f := pullback.snd ((U.transport g.asIso).hom) (pullback.fst (U.proj t) (U.proj t)))
    (g := graph (U := U) t h)
  let L₂ : pullback (pullback.snd ((U.transport g.asIso).hom) (pullback.fst (U.proj t) (U.proj t)))
      (graph (U := U) t h) ⟶ pullback ((U.transport g.asIso).hom) (𝟙 (U.cover t)) :=
    pullback.lift (pullback.fst _ _ ≫ pullback.fst _ _) (pullback.snd _ _) (by
      rw [Category.assoc, pullback.condition, Category.comp_id, ← Category.assoc, c₂,
        Category.assoc, hhf, Category.comp_id])
  have hL₂ : L₂ ≫ m₂ = pullback.fst _ _ := by
    refine pullback.hom_ext ?_ ?_
    · simp [m₂, L₂]
    · simp only [m₂, L₂, Category.assoc, pullback.lift_snd, pullback.lift_snd_assoc]
      exact c₂.symm
  -- the composite is the graph of `h * g`
  have hc : pullback.snd ((U.transport g.asIso).hom) (𝟙 (U.cover t)) =
      pullback.fst ((U.transport g.asIso).hom) (𝟙 (U.cover t)) ≫ (U.transport g.asIso).hom := by
    rw [← Category.comp_id (pullback.snd _ _), ← pullback.condition]
  have key : m₂ ≫ m₁ ≫ tripleProj₁₃ (U.proj t) =
      pullback.fst _ _ ≫ graph (U := U) t (h * g) := by
    refine pullback.hom_ext ?_ ?_
    · simp only [m₁, m₂, Category.assoc, pullback.lift_fst, pullback.lift_fst_assoc,
        Category.comp_id, graph_fst]
    · simp only [m₁, m₂, Category.assoc, pullback.lift_snd, pullback.lift_snd_assoc,
        Category.comp_id, graph_snd]
      rw [hc, Category.assoc, transport_mul_hom]
  have hp₁₃ : (tripleProj₁₃ (U.proj t)).base τ =
      (m₂ ≫ m₁ ≫ tripleProj₁₃ (U.proj t)).base (L₂.base ρ₂) := by
    simp only [Scheme.Hom.comp_apply]
    rw [← Scheme.Hom.comp_apply L₂ m₂, hL₂, hρ₂, hτ]
  rw [hp₁₃, loop_apply_of_eq_comp t _ _ _ key]

end AlgebraicGeometry.Scheme.UniversalCovers
