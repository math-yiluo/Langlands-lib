/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.NearbyCycles.ExchangeCompRetraction
public import WeilConjectures.Tactic.ExactModProofs
public import WeilConjectures.Tactic.TransportExact

/-!

# Averaging retractions of pullback exchanges along composites of morphisms of models

Call a morphism `a` in a preadditive category *split by an average* if it has a retraction `r`
such that `n • (r ≫ a)` is a sum `∑ i ∈ s, ρ i` of given endomorphisms (the inclusion of the
invariants of a finite group of order `n` acting through the `ρ i`). This file transports this
property along the composition law of pullback exchanges
(`NearbyCyclesModel.Hom.pullbackExchange_comp_app_of_eq`), for averages of actions of
automorphisms of models (`NearbyCyclesModel.Hom.autAction`):

* along a composite whose second factor has invertible exchange
  (`NearbyCyclesModel.exists_retraction_pullbackExchange_comp_of_isIso`), and conversely
  (`NearbyCyclesModel.exists_retraction_pullbackExchange_of_comp_of_isIso`);
* along a composite whose first factor has invertible exchange intertwining the actions
  (`NearbyCyclesModel.exists_retraction_pullbackExchange_comp_of_isIso_left`);
* along an isomorphism of complexes
  (`NearbyCyclesModel.exists_retraction_pullbackExchange_app_of_isIso`);
* for the composite `M'' ⟶ N_Ω ⟶ N ⟶ M` of a morphism with invertible exchange, the projection
  of a Galois layer and a morphism with invertible exchange
  (`NearbyCyclesModel.exists_retraction_pullbackExchange_of_comp_galoisLayer`), the shape of the
  generic-slicing identification of nearby cycles with invariants (SGA 4½, [Th. finitude], §3.7).

The statements are first proved for abstract functors and natural transformations
(`CategoryTheory.exists_retraction_app_of_comp_of_isIso` and its variants), then instantiated in
the abstract setting of morphisms of models, so that the concrete applications only unify the
hypotheses and conclusions of the latter.

-/

@[expose] public section

universe u

open CategoryTheory

open scoped CategoryTheory.Functor CategoryTheory.Obj

/-- **Sums over a quotient by a kernel**: for a surjective `π : G →* H` onto a finite group and
`f : G → M` invariant under right multiplication by the kernel, the sum of `f` over
representatives of `G ⧸ ker π` is the sum over any section `s` of `π`. -/
theorem MonoidHom.sum_quotient_ker_out_eq_sum {G H M : Type*} [Group G] [Group H] [Fintype H]
    [AddCommMonoid M] (π : G →* H) (hπ : Function.Surjective π) [Fintype (G ⧸ π.ker)]
    (f : G → M) (hf : ∀ σ, ∀ v ∈ π.ker, f (σ * v) = f σ) (s : H → G) (hs : ∀ τ, π (s τ) = τ) :
    ∑ σ : G ⧸ π.ker, f σ.out = ∑ τ, f (s τ) := by
  refine Fintype.sum_equiv (QuotientGroup.quotientKerEquivOfSurjective π hπ).toEquiv _ _
    fun σ ↦ ?_
  have he : (QuotientGroup.quotientKerEquivOfSurjective π hπ).toEquiv σ = π σ.out := by
    conv_lhs => rw [← QuotientGroup.out_eq' σ]
    rfl
  rw [he, ← hf σ.out (σ.out⁻¹ * s (π σ.out)) (by simp [hs]), mul_inv_cancel_left]

/-- The quotient of `G` by the kernel of a surjection onto a finite group `H` has `|H|`
elements. -/
theorem MonoidHom.card_quotient_ker {G H : Type*} [Group G] [Group H] [Fintype H]
    (π : G →* H) (hπ : Function.Surjective π) [Fintype (G ⧸ π.ker)] :
    Fintype.card (G ⧸ π.ker) = Fintype.card H :=
  Fintype.card_congr (QuotientGroup.quotientKerEquivOfSurjective π hπ).toEquiv

/-- **Reindexing an average over a quotient by a kernel**: if `|H| • x` is the sum over `H` of
`f ∘ s` for a section `s` of a surjection `π : G →* H` and `f` invariant under the kernel, then
`|G ⧸ ker π| • x` is the sum of `f` over representatives of `G ⧸ ker π`. The two (equal)
instances `Fintype H` are arbitrary, so that the hypothesis can be used as produced. -/
theorem MonoidHom.card_nsmul_eq_sum_quotient_ker {G H M : Type*} [Group G] [Group H]
    {iH iH' : Fintype H} [AddCommMonoid M] (π : G →* H) (hπ : Function.Surjective π)
    [Fintype (G ⧸ π.ker)] (f : G → M) (hf : ∀ σ, ∀ v ∈ π.ker, f (σ * v) = f σ) (s : H → G)
    (hs : ∀ τ, π (s τ) = τ) (x : M)
    (h : @Fintype.card H iH • x = ∑ τ ∈ @Finset.univ H iH', f (s τ)) :
    Fintype.card (G ⧸ π.ker) • x = ∑ σ : G ⧸ π.ker, f σ.out := by
  obtain rfl := Subsingleton.elim iH iH'
  rw [π.card_quotient_ker hπ, π.sum_quotient_ker_out_eq_sum hπ f hf s hs]
  exact h

/-- A variant of `MonoidHom.card_nsmul_eq_sum_quotient_ker` where the summands `g τ` and all the
instances are read off the hypothesis `h`, and only compared with `f (s τ)` (`hg`). -/
theorem MonoidHom.card_nsmul_eq_sum_quotient_ker' {G H M : Type*} [Group G] [Group H]
    {iH iH' : Fintype H} {iM : AddCommMonoid M} {x : M} {g : H → M}
    (h : @Fintype.card H iH • x = ∑ τ ∈ @Finset.univ H iH', g τ) (π : G →* H)
    (hπ : Function.Surjective π) [Fintype (G ⧸ π.ker)] (f : G → M)
    (hf : ∀ σ, ∀ v ∈ π.ker, f (σ * v) = f σ) (s : H → G) (hs : ∀ τ, π (s τ) = τ)
    (hg : ∀ τ, g τ = f (s τ)) :
    Fintype.card (G ⧸ π.ker) • x = ∑ σ : G ⧸ π.ker, f σ.out :=
  π.card_nsmul_eq_sum_quotient_ker hπ f hf s hs x (h.trans (Finset.sum_congr rfl fun τ _ ↦ hg τ))

namespace CategoryTheory

variable {C : Type*} [Category C] [Preadditive C]

/-- **Transporting a retraction with an average along a commutative square of isomorphisms**: if
`a ≫ v = u ≫ b` with `u`, `v` invertible and `b` has a retraction `r` with `n • (r ≫ b) = e`,
then `a` has a retraction `r'` with `n • (r' ≫ a) = v ≫ e ≫ v⁻¹`. -/
theorem exists_retraction_nsmul_of_comp_eq_comp {P Q P' Q' : C} (a : P ⟶ Q) (b : P' ⟶ Q')
    (u : P ⟶ P') (v : Q ⟶ Q') [IsIso u] [IsIso v] (h : a ≫ v = u ≫ b) (n : ℕ) (e : Q' ⟶ Q')
    (r : Q' ⟶ P') (hr : b ≫ r = 𝟙 _) (havg : n • (r ≫ b) = e) :
    ∃ r' : Q ⟶ P, a ≫ r' = 𝟙 _ ∧ n • (r' ≫ a) = v ≫ e ≫ inv v := by
  have ha : a = u ≫ b ≫ inv v := by rw [← reassoc_of% h, IsIso.hom_inv_id, Category.comp_id]
  refine ⟨v ≫ r ≫ inv u, ?_, ?_⟩
  · rw [ha]
    simp [reassoc_of% hr]
  · rw [ha, ← havg]
    simp

/-- A sum of natural endomorphisms of a functor `Ψ` is invariant under conjugation by `Ψ` of an
isomorphism. -/
lemma sum_conj_eq_of_naturality {D : Type*} [Category D] (Ψ : D ⥤ C) {ι : Type*}
    (s : Finset ι) (act : ι → ∀ Y : D, Ψ.obj Y ⟶ Ψ.obj Y)
    (hact : ∀ i {Y Y' : D} (g : Y ⟶ Y'), act i Y ≫ Ψ.map g = Ψ.map g ≫ act i Y')
    {Y Y' : D} (w : Y ⟶ Y') [IsIso w] :
    Ψ.map w ≫ (∑ i ∈ s, act i Y') ≫ inv (Ψ.map w) = ∑ i ∈ s, act i Y := by
  rw [Preadditive.sum_comp, Preadditive.comp_sum]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [← reassoc_of% hact i w, IsIso.hom_inv_id, Category.comp_id]

/-- **Transporting an average along `Ψ` of an isomorphism**: if `a ≫ Ψ w = c ≫ e ≫ b` with `w`,
`c`, `e` invertible and `a` is split with average `∑ i ∈ s, act i Y` of natural endomorphisms
of `Ψ`, then `b` is split with average `∑ i ∈ s, act i Y'`. -/
theorem exists_retraction_of_comp_map_eq {D : Type*} [Category D] (Ψ : D ⥤ C)
    {ι : Type*} (s : Finset ι) (act : ι → ∀ Y : D, Ψ.obj Y ⟶ Ψ.obj Y)
    {Y Y' : D} (w : Y ⟶ Y') [IsIso w] {P P' P'' : C} (a : P ⟶ Ψ.obj Y) (c : P ⟶ P'')
    (e : P'' ⟶ P') [IsIso c] [IsIso e] (b : P' ⟶ Ψ.obj Y') (h : a ≫ Ψ.map w = c ≫ e ≫ b)
    (n : ℕ) (r : Ψ.obj Y ⟶ P) (hr : a ≫ r = 𝟙 _) (havg : n • (r ≫ a) = ∑ i ∈ s, act i Y)
    (hact : ∀ i {Y Y' : D} (g : Y ⟶ Y'), act i Y ≫ Ψ.map g = Ψ.map g ≫ act i Y') :
    ∃ r' : Ψ.obj Y' ⟶ P', b ≫ r' = 𝟙 _ ∧ n • (r' ≫ b) = ∑ i ∈ s, act i Y' := by
  obtain ⟨r', hr', havg'⟩ := exists_retraction_nsmul_of_comp_eq_comp b a (inv (c ≫ e))
    (inv (Ψ.map w)) (by rw [IsIso.eq_inv_comp, Category.assoc, ← reassoc_of% h,
      IsIso.hom_inv_id, Category.comp_id]) n _ r hr havg
  refine ⟨r', hr', havg'.trans ?_⟩
  rw [IsIso.inv_inv, Preadditive.sum_comp, Preadditive.comp_sum]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [hact i w, IsIso.inv_hom_id_assoc]


section Exchange

variable {DP DN DM SP SN SM : Type*} [Category DP] [Category DN] [Category DM] [Category SP]
  [Category SN] [Category SM] [Preadditive SM]
  {ΨP : DP ⥤ SP} {ΨN : DN ⥤ SN} {ΨM : DM ⥤ SM}
  {Lf : DN ⥤ DM} {Lg : DP ⥤ DN} {Lfg : DP ⥤ DM} {Lf' : SN ⥤ SM} {Lg' : SP ⥤ SN}
  {Lfg' : SP ⥤ SM}

/-- **Composition law and averages, invertible second factor**: let `αφψ`, `αψ`, `αφ` satisfy the
composition law `hx` of pullback exchanges
(`NearbyCyclesModel.Hom.pullbackExchange_comp_app_of_eq`).
If `αψ` is invertible at `C` and `αφ` is split at `Lg C` with average `∑ i ∈ s, act i`, then so
is `αφψ` at `C`. -/
theorem exists_retraction_app_of_comp_of_isIso (αφψ : ΨP ⋙ Lfg' ⟶ Lfg ⋙ ΨM)
    (αψ : ΨP ⋙ Lg' ⟶ Lg ⋙ ΨN) (αφ : ΨN ⋙ Lf' ⟶ Lf ⋙ ΨM) (cfg : Lfg ≅ Lg ⋙ Lf)
    (cfg' : Lfg' ≅ Lg' ⋙ Lf') (C : DP)
    (hx : αφψ.app C ≫ ΨM.map (cfg.hom.app C) =
      cfg'.hom.app (ΨP.obj C) ≫ Lf'.map (αψ.app C) ≫ αφ.app (Lg.obj C))
    (hψ : IsIso (αψ.app C)) {ι : Type*} (s : Finset ι)
    (act : ι → ∀ Y : DM, ΨM.obj Y ⟶ ΨM.obj Y)
    (n : ℕ) (h : ∃ r, αφ.app (Lg.obj C) ≫ r = 𝟙 _ ∧
      n • (r ≫ αφ.app (Lg.obj C)) = ∑ i ∈ s, act i (Lf.obj (Lg.obj C)))
    (hact : ∀ i {Y Y' : DM} (g : Y ⟶ Y'), act i Y ≫ ΨM.map g = ΨM.map g ≫ act i Y') :
    ∃ r', αφψ.app C ≫ r' = 𝟙 _ ∧ n • (r' ≫ αφψ.app C) = ∑ i ∈ s, act i (Lfg.obj C) := by
  obtain ⟨r, hr, havg⟩ := h
  obtain ⟨r', hr', havg'⟩ := exists_retraction_nsmul_of_comp_eq_comp (αφψ.app C)
    (αφ.app (Lg.obj C)) (cfg'.hom.app (ΨP.obj C) ≫ Lf'.map (αψ.app C)) (ΨM.map (cfg.hom.app C))
    (by rw [hx, Category.assoc]) n _ r hr havg
  exact ⟨r', hr', havg'.trans (sum_conj_eq_of_naturality ΨM s act hact (cfg.hom.app C))⟩

/-- **Composition law and averages, converse**: under the composition law `hx`, if `αψ` is
invertible at `C` and `αφψ` is split at `C` with average `∑ i ∈ s, act i`, then so is `αφ` at
`Lg C`. -/
theorem exists_retraction_app_of_comp_of_isIso' (αφψ : ΨP ⋙ Lfg' ⟶ Lfg ⋙ ΨM)
    (αψ : ΨP ⋙ Lg' ⟶ Lg ⋙ ΨN) (αφ : ΨN ⋙ Lf' ⟶ Lf ⋙ ΨM) (cfg : Lfg ≅ Lg ⋙ Lf)
    (cfg' : Lfg' ≅ Lg' ⋙ Lf') (C : DP)
    (hx : αφψ.app C ≫ ΨM.map (cfg.hom.app C) =
      cfg'.hom.app (ΨP.obj C) ≫ Lf'.map (αψ.app C) ≫ αφ.app (Lg.obj C))
    (hψ : IsIso (αψ.app C)) {ι : Type*} (s : Finset ι)
    (act : ι → ∀ Y : DM, ΨM.obj Y ⟶ ΨM.obj Y)
    (n : ℕ) (h : ∃ r, αφψ.app C ≫ r = 𝟙 _ ∧ n • (r ≫ αφψ.app C) = ∑ i ∈ s, act i (Lfg.obj C))
    (hact : ∀ i {Y Y' : DM} (g : Y ⟶ Y'), act i Y ≫ ΨM.map g = ΨM.map g ≫ act i Y') :
    ∃ r', αφ.app (Lg.obj C) ≫ r' = 𝟙 _ ∧
      n • (r' ≫ αφ.app (Lg.obj C)) = ∑ i ∈ s, act i (Lf.obj (Lg.obj C)) := by
  obtain ⟨r, hr, havg⟩ := h
  obtain ⟨r', hr', havg'⟩ := exists_retraction_nsmul_of_comp_eq_comp (αφ.app (Lg.obj C))
    (αφψ.app C) (inv (cfg'.hom.app (ΨP.obj C) ≫ Lf'.map (αψ.app C)))
    (inv (ΨM.map (cfg.hom.app C)))
    (by
      rw [IsIso.eq_inv_comp]
      simp only [Category.assoc]
      rw [← reassoc_of% hx, IsIso.hom_inv_id, Category.comp_id]) n _ r hr havg
  refine ⟨r', hr', havg'.trans ?_⟩
  rw [IsIso.inv_inv, Preadditive.sum_comp, Preadditive.comp_sum]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [hact i (cfg.hom.app C), IsIso.inv_hom_id_assoc]
  rfl

end Exchange

/-- **Averages through an endofunctor isomorphic to the identity on two objects**: if
`F β ≫ ηQ = ηP ≫ β` with `ηP`, `ηQ` invertible and `F (actQ i) ≫ ηQ = ηQ ≫ actQ i`, a split
`β` with average `∑ i ∈ s, actQ i` gives a split `F β` with average `∑ i ∈ s, F (actQ i)`. -/
theorem exists_retraction_map_of_comp_eq {D : Type*} [Category D] [Preadditive D] (F : D ⥤ D)
    {P Q : D} (β : P ⟶ Q) (ηP : F.obj P ⟶ P) (ηQ : F.obj Q ⟶ Q) [IsIso ηP] [IsIso ηQ]
    (hβ : F.map β ≫ ηQ = ηP ≫ β) {ι : Type*} (s : Finset ι) {actQ : ι → (Q ⟶ Q)} (n : ℕ)
    (h : ∃ r, β ≫ r = 𝟙 _ ∧ n • (r ≫ β) = ∑ i ∈ s, actQ i)
    (hact : ∀ i, F.map (actQ i) ≫ ηQ = ηQ ≫ actQ i) :
    ∃ r, F.map β ≫ r = 𝟙 _ ∧ n • (r ≫ F.map β) = ∑ i ∈ s, F.map (actQ i) := by
  obtain ⟨r, hr, havg⟩ := h
  obtain ⟨r', hr', havg'⟩ := exists_retraction_nsmul_of_comp_eq_comp (F.map β) β ηP ηQ hβ n _ r
    hr havg
  refine ⟨r', hr', havg'.trans ?_⟩
  rw [Preadditive.sum_comp, Preadditive.comp_sum]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [← reassoc_of% hact i, IsIso.hom_inv_id, Category.comp_id]

/-- **Composition law and averages, invertible first factor**: under the composition law
`hx`, if `αφ` is invertible at `Lg C` and intertwines `actN` with `act` (`hint`), and `Lf' (αψ C)`
is split with average `∑ i ∈ s, Lf' (actN i)`, then `αφψ` is split at `C` with average
`∑ i ∈ s, act i`. -/
theorem exists_retraction_app_of_comp_of_isIso_left {DP DN DM SP SN SM : Type*} [Category DP]
    [Category DN] [Category DM] [Category SP] [Category SN] [Category SM] [Preadditive SM]
    {ΨP : DP ⥤ SP} {ΨN : DN ⥤ SN} {ΨM : DM ⥤ SM} {Lf : DN ⥤ DM} {Lg : DP ⥤ DN}
    {Lfg : DP ⥤ DM} {Lf' : SN ⥤ SM} {Lg' : SP ⥤ SN} {Lfg' : SP ⥤ SM}
    (αφψ : ΨP ⋙ Lfg' ⟶ Lfg ⋙ ΨM)
    (αψ : ΨP ⋙ Lg' ⟶ Lg ⋙ ΨN) (αφ : ΨN ⋙ Lf' ⟶ Lf ⋙ ΨM) (cfg : Lfg ≅ Lg ⋙ Lf)
    (cfg' : Lfg' ≅ Lg' ⋙ Lf') (C : DP)
    (hx : αφψ.app C ≫ ΨM.map (cfg.hom.app C) =
      cfg'.hom.app (ΨP.obj C) ≫ Lf'.map (αψ.app C) ≫ αφ.app (Lg.obj C))
    (hφ : IsIso (αφ.app (Lg.obj C))) {ι : Type*} (s : Finset ι)
    (act : ι → ∀ Y : DM, ΨM.obj Y ⟶ ΨM.obj Y) (actN : ι → ∀ Y : DN, ΨN.obj Y ⟶ ΨN.obj Y)
    (n : ℕ) (h : ∃ r, Lf'.map (αψ.app C) ≫ r = 𝟙 _ ∧
      n • (r ≫ Lf'.map (αψ.app C)) = ∑ i ∈ s, Lf'.map (actN i (Lg.obj C)))
    (hint : ∀ i (D : DN), αφ.app D ≫ act i (Lf.obj D) = Lf'.map (actN i D) ≫ αφ.app D)
    (hact : ∀ i {Y Y' : DM} (g : Y ⟶ Y'), act i Y ≫ ΨM.map g = ΨM.map g ≫ act i Y') :
    ∃ r', αφψ.app C ≫ r' = 𝟙 _ ∧ n • (r' ≫ αφψ.app C) = ∑ i ∈ s, act i (Lfg.obj C) := by
  obtain ⟨r, hr, havg⟩ := h
  obtain ⟨r₂, hr₂, havg₂⟩ := exists_retraction_nsmul_of_comp_eq_comp (αφψ.app C)
    (Lf'.map (αψ.app C)) (cfg'.hom.app (ΨP.obj C)) (ΨM.map (cfg.hom.app C) ≫
      inv (αφ.app (Lg.obj C))) (by rw [← Category.assoc, hx, Category.assoc, Category.assoc,
      IsIso.hom_inv_id, Category.comp_id]) n _ r hr havg
  refine ⟨r₂, hr₂, havg₂.trans ?_⟩
  rw [← sum_conj_eq_of_naturality ΨM s act hact (cfg.hom.app C), Preadditive.sum_comp,
    Preadditive.comp_sum, Preadditive.sum_comp, Preadditive.comp_sum]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  simp [← reassoc_of% hint i]

/-- **Averages transported along an isomorphism of objects**: for a natural transformation
`α : F ⟶ L ⋙ Ψ` and natural endomorphisms `act i` of `Ψ`, if `α` is split at `A` with average
`∑ i ∈ s, act i (L A)`, it is split at any `A' ≅ A` with average `∑ i ∈ s, act i (L A')`. -/
theorem exists_retraction_app_of_isIso {D E : Type*} [Category D] [Category E] (F : D ⥤ C)
    (L : D ⥤ E) (Ψ : E ⥤ C) (α : F ⟶ L ⋙ Ψ) {ι : Type*} (s : Finset ι)
    (act : ι → ∀ Y : E, Ψ.obj Y ⟶ Ψ.obj Y) {A A' : D} (w : A ⟶ A') [IsIso w] (n : ℕ)
    (h : ∃ r, α.app A ≫ r = 𝟙 _ ∧ n • (r ≫ α.app A) = ∑ i ∈ s, act i (L.obj A))
    (hact : ∀ i {Y Y' : E} (g : Y ⟶ Y'), act i Y ≫ Ψ.map g = Ψ.map g ≫ act i Y') :
    ∃ r', α.app A' ≫ r' = 𝟙 _ ∧ n • (r' ≫ α.app A') = ∑ i ∈ s, act i (L.obj A') := by
  obtain ⟨r, hr, havg⟩ := h
  exact exists_retraction_of_comp_map_eq Ψ s act (L.map w) (α.app A) (F.map w) (𝟙 _) (α.app A')
    (by simp) n r hr havg hact

end CategoryTheory

namespace AlgebraicGeometry.ProEtale.CondensedRing.NearbyCyclesModel

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
  {X₀ X₁ X₂ S₀ S₁ S₂ : Scheme.{u}} {M₀ : NearbyCyclesModel X₀ S₀}
  {M₁ : NearbyCyclesModel X₁ S₁} {M₂ : NearbyCyclesModel X₂ S₂} {f : X₀ ⟶ X₁} {f' : S₀ ⟶ S₁}
  {g : X₁ ⟶ X₂} {g' : S₁ ⟶ S₂} {fg : X₀ ⟶ X₂} {fg' : S₀ ⟶ S₂}

/-- **Averages along a composite with invertible second exchange**: let `χ` have the components
of `ρ ≫ ψ` (`htot`, `hgen`). If the pullback exchange of `ψ` is invertible at `C` and that of
`ρ` is split at `Lg C` with average the sum of the actions of automorphisms `σ i` of `M₀`, then so
is that of `χ` at `C`. -/
theorem exists_retraction_pullbackExchange_comp_of_isIso (ρ : M₀.Hom M₁ f f')
    (ψ : M₁.Hom M₂ g g') (χ : M₀.Hom M₂ fg fg') (h : f ≫ g = fg) (h' : f' ≫ g' = fg')
    (htot : ρ.total ≫ ψ.total = χ.total) (hgen : ρ.generic ≫ ψ.generic = χ.generic)
    (C : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X₂) Ab.{u + 1})
      (condensedRingObj Λ X₂))) (hψi : IsIso ((ψ.pullbackExchange Λ).app C)) {ι : Type*}
    (s : Finset ι) (σ : ι → M₀.Hom M₀ (𝟙 X₀) (𝟙 S₀))
    (n : ℕ) (hρ : ∃ r, (ρ.pullbackExchange Λ).app (L((g)^*⟦Λ⟧).obj C) ≫ r = 𝟙 _ ∧
      n • (r ≫ (ρ.pullbackExchange Λ).app (L((g)^*⟦Λ⟧).obj C)) =
        ∑ i ∈ s, (σ i).autAction Λ (L((f)^*⟦Λ⟧).obj (L((g)^*⟦Λ⟧).obj C))) :
    ∃ r', (χ.pullbackExchange Λ).app C ≫ r' = 𝟙 _ ∧
      n • (r' ≫ (χ.pullbackExchange Λ).app C) =
        ∑ i ∈ s, (σ i).autAction Λ (L((fg)^*⟦Λ⟧).obj C) := by
  have hx := ρ.pullbackExchange_comp_app_of_eq Λ ψ χ h h' htot hgen C
  have t := exists_retraction_app_of_comp_of_isIso (χ.pullbackExchange Λ) (ψ.pullbackExchange Λ)
    (ρ.pullbackExchange Λ) (leftDerivedUpperStarCompOfEq Λ h) (leftDerivedUpperStarCompOfEq Λ h')
    C hx (by exact_mod_proofs hψi) s (fun i ↦ (σ i).autAction Λ) n (by exact_mod_proofs hρ)
    (fun i _ _ u ↦ Hom.autAction_naturality Λ (σ i) u)
  exact t

/-- **Averages along a composite with invertible second exchange, converse**: if the pullback
exchange of `ψ` is invertible at `C` and that of `χ` (with the components of `ρ ≫ ψ`) is split
at `C` with average the sum of the actions of the `σ i`, then so is that of `ρ` at `Lg C`. -/
theorem exists_retraction_pullbackExchange_of_comp_of_isIso (ρ : M₀.Hom M₁ f f')
    (ψ : M₁.Hom M₂ g g') (χ : M₀.Hom M₂ fg fg') (h : f ≫ g = fg) (h' : f' ≫ g' = fg')
    (htot : ρ.total ≫ ψ.total = χ.total) (hgen : ρ.generic ≫ ψ.generic = χ.generic)
    (C : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X₂) Ab.{u + 1})
      (condensedRingObj Λ X₂))) (hψi : IsIso ((ψ.pullbackExchange Λ).app C)) {ι : Type*}
    (s : Finset ι) (σ : ι → M₀.Hom M₀ (𝟙 X₀) (𝟙 S₀)) (n : ℕ)
    (hχ : ∃ r, (χ.pullbackExchange Λ).app C ≫ r = 𝟙 _ ∧
      n • (r ≫ (χ.pullbackExchange Λ).app C) = ∑ i ∈ s, (σ i).autAction Λ (L((fg)^*⟦Λ⟧).obj C)) :
    ∃ r', (ρ.pullbackExchange Λ).app (L((g)^*⟦Λ⟧).obj C) ≫ r' = 𝟙 _ ∧
      n • (r' ≫ (ρ.pullbackExchange Λ).app (L((g)^*⟦Λ⟧).obj C)) =
        ∑ i ∈ s, (σ i).autAction Λ (L((f)^*⟦Λ⟧).obj (L((g)^*⟦Λ⟧).obj C)) := by
  have hx := ρ.pullbackExchange_comp_app_of_eq Λ ψ χ h h' htot hgen C
  have t := exists_retraction_app_of_comp_of_isIso' (χ.pullbackExchange Λ)
    (ψ.pullbackExchange Λ) (ρ.pullbackExchange Λ) (leftDerivedUpperStarCompOfEq Λ h)
    (leftDerivedUpperStarCompOfEq Λ h') C hx (by exact_mod_proofs hψi) s
    (fun i ↦ (σ i).autAction Λ) n (by exact_mod_proofs hχ)
    (fun i _ _ u ↦ Hom.autAction_naturality Λ (σ i) u)
  exact_mod_proofs t

/-- **Averages along a composite with invertible first exchange**: let `χ` have the components
of `ρ ≫ ψ`, with `ρ` over the identity of special fibres. If the pullback exchange of `ρ` is
invertible at `Lg C` and intertwines the actions of automorphisms `τ i` of `M₁` with those of
automorphisms `σ i` of `M₀`, and that of `ψ` is split at `C` with average the sum of the actions
of the `τ i`, then that of `χ` is split at `C` with average the sum of the actions of the `σ i`.
The exchange of `L(𝟙)^*` is handled by `leftDerivedUpperStarId`. -/
theorem exists_retraction_pullbackExchange_comp_of_isIso_left {M₁ : NearbyCyclesModel X₁ S₀}
    {g' : S₀ ⟶ S₂} (ρ : M₀.Hom M₁ f (𝟙 S₀))
    (ψ : M₁.Hom M₂ g g') (χ : M₀.Hom M₂ fg fg') (h : f ≫ g = fg) (h' : 𝟙 S₀ ≫ g' = fg')
    (htot : ρ.total ≫ ψ.total = χ.total) (hgen : ρ.generic ≫ ψ.generic = χ.generic)
    (C : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X₂) Ab.{u + 1})
      (condensedRingObj Λ X₂))) (hρi : IsIso ((ρ.pullbackExchange Λ).app (L((g)^*⟦Λ⟧).obj C)))
    {ι : Type*} (s : Finset ι) (σ : ι → M₀.Hom M₀ (𝟙 X₀) (𝟙 S₀))
    (τ : ι → M₁.Hom M₁ (𝟙 X₁) (𝟙 S₀)) (n : ℕ)
    (hψ : ∃ r, (ψ.pullbackExchange Λ).app C ≫ r = 𝟙 _ ∧
      n • (r ≫ (ψ.pullbackExchange Λ).app C) = ∑ i ∈ s, (τ i).autAction Λ (L((g)^*⟦Λ⟧).obj C))
    (hint : ∀ i D, (ρ.pullbackExchange Λ).app D ≫ (σ i).autAction Λ (L((f)^*⟦Λ⟧).obj D) =
      L((𝟙 S₀)^*⟦Λ⟧).map ((τ i).autAction Λ D) ≫ (ρ.pullbackExchange Λ).app D) :
    ∃ r', (χ.pullbackExchange Λ).app C ≫ r' = 𝟙 _ ∧
      n • (r' ≫ (χ.pullbackExchange Λ).app C) =
        ∑ i ∈ s, (σ i).autAction Λ (L((fg)^*⟦Λ⟧).obj C) := by
  have hF := exists_retraction_map_of_comp_eq _ ((ψ.pullbackExchange Λ).app C)
    ((leftDerivedUpperStarId Λ S₀).hom.app _) ((leftDerivedUpperStarId Λ S₀).hom.app _)
    ((leftDerivedUpperStarId Λ S₀).hom.naturality _) s n hψ
    (fun i ↦ (leftDerivedUpperStarId Λ S₀).hom.naturality _)
  have hx := ρ.pullbackExchange_comp_app_of_eq Λ ψ χ h h' htot hgen C
  have t := exists_retraction_app_of_comp_of_isIso_left (χ.pullbackExchange Λ)
    (ψ.pullbackExchange Λ) (ρ.pullbackExchange Λ) (leftDerivedUpperStarCompOfEq Λ h)
    (leftDerivedUpperStarCompOfEq Λ h') C hx (by exact_mod_proofs hρi) s
    (fun i ↦ (σ i).autAction Λ) (fun i ↦ (τ i).autAction Λ) n
    (by beta_reduce; transport_exact hF) (fun i D ↦ by beta_reduce; transport_exact hint i D)
    (fun i _ _ u ↦ Hom.autAction_naturality Λ (σ i) u)
  exact_mod_proofs t

/-- **Averages along an isomorphism of complexes**: if the pullback exchange of `ρ` is split at
`A` with average the sum of the actions of the `σ i`, then so it is at any complex isomorphic to
`A`. -/
theorem exists_retraction_pullbackExchange_app_of_isIso {X₀ X₁ S₀ S₁ : Scheme.{u}}
    {M₀ : NearbyCyclesModel X₀ S₀} {M₁ : NearbyCyclesModel X₁ S₁} {f : X₀ ⟶ X₁}
    {f' : S₀ ⟶ S₁} (ρ : M₀.Hom M₁ f f') {ι : Type*} (s : Finset ι)
    (σ : ι → M₀.Hom M₀ (𝟙 X₀) (𝟙 S₀)) {A A' : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X₁)
      Ab.{u + 1}) (condensedRingObj Λ X₁))} (w : A ⟶ A') [IsIso w] (n : ℕ)
    (hρ : ∃ r, (ρ.pullbackExchange Λ).app A ≫ r = 𝟙 _ ∧
      n • (r ≫ (ρ.pullbackExchange Λ).app A) = ∑ i ∈ s, (σ i).autAction Λ (L((f)^*⟦Λ⟧).obj A)) :
    ∃ r', (ρ.pullbackExchange Λ).app A' ≫ r' = 𝟙 _ ∧
      n • (r' ≫ (ρ.pullbackExchange Λ).app A') =
        ∑ i ∈ s, (σ i).autAction Λ (L((f)^*⟦Λ⟧).obj A') := by
  have t := exists_retraction_app_of_isIso _ _ _ (ρ.pullbackExchange Λ) s
    (fun i ↦ (σ i).autAction Λ) w n (by exact_mod_proofs hρ)
    (fun i _ _ u ↦ Hom.autAction_naturality Λ (σ i) u)
  exact_mod_proofs t

/-- **Averages along a composite through a Galois layer** (the shape of the generic-slicing
identification, SGA 4½, [Th. finitude], §3.7): let `φ : M'' ⟶ M` have the components of
`ρ ≫ ψ ≫ χ` with `ρ : M'' ⟶ N₁` and `ψ : N₁ ⟶ N` over the identities of `X` and of the special
fibre. If the pullback exchanges of `ρ` (everywhere) and of `χ` (at `A`) are invertible, `ρ`
intertwines the actions of automorphisms `σ i` of `M''` and `τ i` of `N₁`, and the exchange
of `ψ` is split at `A` with average the sum of the actions of the `τ i`, then the exchange of `φ`
is split at `A` with average the sum of the actions of the `σ i`. -/
theorem exists_retraction_pullbackExchange_of_comp_galoisLayer {X S S' : Scheme.{u}}
    {M'' N₁ N : NearbyCyclesModel X S} {M : NearbyCyclesModel X S'} {f' : S ⟶ S'}
    (ρ : M''.Hom N₁ (𝟙 X) (𝟙 S)) (ψ : N₁.Hom N (𝟙 X) (𝟙 S)) (χ : N.Hom M (𝟙 X ≫ 𝟙 X) (𝟙 S ≫ f'))
    (φ : M''.Hom M (𝟙 X) f') (htot : (ρ.total ≫ ψ.total) ≫ χ.total = φ.total)
    (hgen : (ρ.generic ≫ ψ.generic) ≫ χ.generic = φ.generic)
    (A : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ X)))
    (hρ : ∀ C, IsIso ((ρ.pullbackExchange Λ).app C)) (hχ : IsIso ((χ.pullbackExchange Λ).app A))
    {ι : Type*} (s : Finset ι) (σ : ι → M''.Hom M'' (𝟙 X) (𝟙 S))
    (τ : ι → N₁.Hom N₁ (𝟙 X) (𝟙 S)) (n : ℕ)
    (hψ : ∃ r, (ψ.pullbackExchange Λ).app A ≫ r = 𝟙 _ ∧
      n • (r ≫ (ψ.pullbackExchange Λ).app A) = ∑ i ∈ s, (τ i).autAction Λ (L((𝟙 X)^*⟦Λ⟧).obj A))
    (hint : ∀ i D, (ρ.pullbackExchange Λ).app D ≫ (σ i).autAction Λ (L((𝟙 X)^*⟦Λ⟧).obj D) =
      L((𝟙 S)^*⟦Λ⟧).map ((τ i).autAction Λ D) ≫ (ρ.pullbackExchange Λ).app D) :
    ∃ r, (φ.pullbackExchange Λ).app A ≫ r = 𝟙 _ ∧
      n • (r ≫ (φ.pullbackExchange Λ).app A) =
        ∑ i ∈ s, (σ i).autAction Λ (L((𝟙 X)^*⟦Λ⟧).obj A) := by
  let i₀ : A ≅ L((𝟙 X ≫ 𝟙 X)^*⟦Λ⟧).obj A :=
    ((leftDerivedUpperStarComp Λ (𝟙 X) (𝟙 X)).app A ≪≫ (leftDerivedUpperStarId Λ X).app _ ≪≫
      (leftDerivedUpperStarId Λ X).app A).symm
  have h₀ := exists_retraction_pullbackExchange_app_of_isIso Λ ψ s τ i₀.hom n hψ
  have h₂ := exists_retraction_pullbackExchange_comp_of_isIso_left Λ ρ ψ (ρ.comp ψ) rfl rfl rfl
    rfl (L((𝟙 X ≫ 𝟙 X)^*⟦Λ⟧).obj A) (hρ _) s σ τ n h₀ hint
  exact exists_retraction_pullbackExchange_comp_of_isIso Λ (ρ.comp ψ) χ φ
    (Category.id_comp _) (by simp) htot hgen A hχ s σ n h₂

/-- **Averages along a composite with invertible second exchange, over the identities**: if the
pullback exchange of `ψ` is invertible at `C` and that of `χ` (with the components of `ρ ≫ ψ`, all
over `𝟙 X`) is split at `C` with average the sum of the actions of the `σ i`, then so is that of
`ρ` at `C`. -/
theorem exists_retraction_pullbackExchange_of_comp_of_isIso_id {X S₀ S₁ S₂ : Scheme.{u}}
    {M₀ : NearbyCyclesModel X S₀} {M₁ : NearbyCyclesModel X S₁} {M₂ : NearbyCyclesModel X S₂}
    {f' : S₀ ⟶ S₁} {g' : S₁ ⟶ S₂} {fg' : S₀ ⟶ S₂} (ρ : M₀.Hom M₁ (𝟙 X) f')
    (ψ : M₁.Hom M₂ (𝟙 X) g') (χ : M₀.Hom M₂ (𝟙 X) fg') (h' : f' ≫ g' = fg')
    (htot : ρ.total ≫ ψ.total = χ.total) (hgen : ρ.generic ≫ ψ.generic = χ.generic)
    (C : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ X))) (hψi : IsIso ((ψ.pullbackExchange Λ).app C)) {ι : Type*}
    (s : Finset ι) (σ : ι → M₀.Hom M₀ (𝟙 X) (𝟙 S₀)) (n : ℕ)
    (hχ : ∃ r, (χ.pullbackExchange Λ).app C ≫ r = 𝟙 _ ∧
      n • (r ≫ (χ.pullbackExchange Λ).app C) = ∑ i ∈ s, (σ i).autAction Λ (L((𝟙 X)^*⟦Λ⟧).obj C)) :
    ∃ r', (ρ.pullbackExchange Λ).app C ≫ r' = 𝟙 _ ∧
      n • (r' ≫ (ρ.pullbackExchange Λ).app C) =
        ∑ i ∈ s, (σ i).autAction Λ (L((𝟙 X)^*⟦Λ⟧).obj C) := by
  have t₁ : ∃ r, (ρ.pullbackExchange Λ).app (L((𝟙 X)^*⟦Λ⟧).obj C) ≫ r = 𝟙 _ ∧
      n • (r ≫ (ρ.pullbackExchange Λ).app (L((𝟙 X)^*⟦Λ⟧).obj C)) =
        ∑ i ∈ s, (σ i).autAction Λ (L((𝟙 X)^*⟦Λ⟧).obj (L((𝟙 X)^*⟦Λ⟧).obj C)) :=
    exists_retraction_pullbackExchange_of_comp_of_isIso Λ (X₀ := X) (X₁ := X) (X₂ := X)
      (S₀ := S₀) (S₁ := S₁) (S₂ := S₂) (M₀ := M₀) (M₁ := M₁) (M₂ := M₂) (f := 𝟙 X)
      (f' := f') (g := 𝟙 X) (g' := g') (fg := 𝟙 X) (fg' := fg') ρ ψ χ (Category.id_comp _) h'
      htot hgen C hψi s σ n hχ
  have : IsIso ((leftDerivedUpperStarId Λ X).app C).hom := Iso.isIso_hom _
  have t₂ := exists_retraction_pullbackExchange_app_of_isIso Λ (X₀ := X) (X₁ := X) (S₀ := S₀)
    (S₁ := S₁) (f := 𝟙 X) ρ s σ (A := L((𝟙 X)^*⟦Λ⟧).obj C) (A' := C)
    ((leftDerivedUpperStarId Λ X).app C).hom n t₁
  exact t₂

/-- `NearbyCyclesModel.exists_retraction_pullbackExchange_of_comp_of_isIso_id` for the actions of
a group `G` through a quotient by a subgroup of finite index acting trivially: the form of the
identification of nearby cycles with invariants. -/
theorem exists_subgroup_pullbackExchange_of_comp_of_isIso_id {X S₀ S₁ S₂ : Scheme.{u}}
    {M₀ : NearbyCyclesModel X S₀} {M₁ : NearbyCyclesModel X S₁} {M₂ : NearbyCyclesModel X S₂}
    {f' : S₀ ⟶ S₁} {g' : S₁ ⟶ S₂} {fg' : S₀ ⟶ S₂} (ρ : M₀.Hom M₁ (𝟙 X) f')
    (ψ : M₁.Hom M₂ (𝟙 X) g') (χ : M₀.Hom M₂ (𝟙 X) fg') (h' : f' ≫ g' = fg')
    (htot : ρ.total ≫ ψ.total = χ.total) (hgen : ρ.generic ≫ ψ.generic = χ.generic)
    (C : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ X))) (hψi : IsIso ((ψ.pullbackExchange Λ).app C)) {G : Type*}
    [Group G] (act : G → M₀.Hom M₀ (𝟙 X) (𝟙 S₀))
    (h : ∃ (V : Subgroup G) (_ : Fintype (G ⧸ V)),
      (∀ σ ∈ V, (act σ).autAction Λ (L((𝟙 X)^*⟦Λ⟧).obj C) = 𝟙 _) ∧
      ∃ r, (χ.pullbackExchange Λ).app C ≫ r = 𝟙 _ ∧
        Fintype.card (G ⧸ V) • (r ≫ (χ.pullbackExchange Λ).app C) =
          ∑ σ : G ⧸ V, (act σ.out).autAction Λ (L((𝟙 X)^*⟦Λ⟧).obj C)) :
    ∃ (V : Subgroup G) (_ : Fintype (G ⧸ V)),
      (∀ σ ∈ V, (act σ).autAction Λ (L((𝟙 X)^*⟦Λ⟧).obj C) = 𝟙 _) ∧
      ∃ r, (ρ.pullbackExchange Λ).app C ≫ r = 𝟙 _ ∧
        Fintype.card (G ⧸ V) • (r ≫ (ρ.pullbackExchange Λ).app C) =
          ∑ σ : G ⧸ V, (act σ.out).autAction Λ (L((𝟙 X)^*⟦Λ⟧).obj C) := by
  obtain ⟨V, hV, htriv, hχ⟩ := h
  exact ⟨V, hV, htriv, exists_retraction_pullbackExchange_of_comp_of_isIso_id Λ (X := X)
    (S₀ := S₀) (S₁ := S₁) (S₂ := S₂) (M₀ := M₀) (M₁ := M₁) (M₂ := M₂) ρ ψ χ h' htot hgen C hψi
    Finset.univ (fun σ : G ⧸ V ↦ act σ.out) _ hχ⟩

end AlgebraicGeometry.ProEtale.CondensedRing.NearbyCyclesModel
