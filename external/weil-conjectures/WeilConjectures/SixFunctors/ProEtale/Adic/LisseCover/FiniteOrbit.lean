/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.Adic.LisseCover.TwistedSheaf

/-!
# Finite orbits of descent cocycles

Let `f : V ⟶ Y` be flat and quasi-compact and `c` a descent cocycle on the constant sheaf `S_V`
(`AlgebraicGeometry.IsDescentCocycle`). For a point `w` of `V` and `s ∈ S`, the *orbit*
`AlgebraicGeometry.orbitAt f c s w` is the set of values `c z s` over the points `z` of
`V ×_Y V` with first coordinate `w`. It is finite, the fibre of `V ×_Y V ⟶ V` over `w` being
quasi-compact, and it is compatible with `c`
(`AlgebraicGeometry.orbitAt_fst`): `orbit (p₁ z) = c z '' orbit (p₂ z)`.

The orbits at the points of `V` lying over a fixed point `η` of `Y` which specializes to every
point form a finite subsheaf of the sheaf defined by `c` as soon as nearby generic points of `V`
are connected by points of `V ×_Y V` close to the diagonal
(`AlgebraicGeometry.IsGenericallyConnected`), a form of local irreducibility which holds for
schemes ind-étale over a normal integral scheme. This is
`AlgebraicGeometry.exists_finite_invariant_subset_of_isGenericallyConnected`. The conclusion
descends along surjective submersive morphisms
(`AlgebraicGeometry.exists_finite_invariant_subset_of_comp`).
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

variable {Y V : Scheme.{u}}

/-- A morphism `f : V ⟶ Y` is *generically connected at `w`* relative to a point `η` of `Y` if
for every open neighbourhood `Ω` of the diagonal point of `w` in `V ×_Y V` there is a
neighbourhood `U` of `w` such that any generizations `a` of a point of `U` and `b` of `w` lying
over `η` are the coordinates of a point of `Ω`. -/
def IsGenericallyConnectedAt (f : V ⟶ Y) (η : Y) (w : V) : Prop :=
  ∀ Ω : Set ↥(pullback f f), IsOpen Ω → (pullback.diagonal f).base w ∈ Ω →
    ∃ U ∈ nhds w, ∀ w₁ ∈ U, ∀ a b : V, a ⤳ w₁ → b ⤳ w → f.base a = η → f.base b = η →
      ∃ z ∈ Ω, (pullback.fst f f).base z = a ∧ (pullback.snd f f).base z = b

/-- A morphism `f : V ⟶ Y` is *generically connected* relative to `η : Y` if it is so at every
point of `V` (`AlgebraicGeometry.IsGenericallyConnectedAt`). -/
def IsGenericallyConnected (f : V ⟶ Y) (η : Y) : Prop :=
  ∀ w, IsGenericallyConnectedAt f η w

section Orbit

variable (f : V ⟶ Y) {S : Type*} (c : ↥(pullback f f) → S → S) (s : S)

/-- The orbit of `s` at a point `w` of `V` under a descent cocycle `c`: the values `c z s` at
the points `z` of `V ×_Y V` with first coordinate `w`. -/
def orbitAt (w : V) : Set S :=
  (fun z ↦ c z s) '' ((pullback.fst f f).base ⁻¹' {w})

variable {f c}

/-- Orbits of descent cocycles along quasi-compact morphisms are finite. -/
lemma finite_orbitAt [QuasiCompact f] (hc : IsDescentCocycle f c) (w : V) :
    (orbitAt f c s w).Finite := by
  let g := V.fromSpecResidueField w
  refine ((hc.isLocallyConstant s).comp_continuous
    (pullback.fst (pullback.fst f f) g).base.hom.continuous).range_finite.subset ?_
  rintro _ ⟨z, hz, rfl⟩
  obtain ⟨p, hp, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := pullback.fst f f) (g := g)
    z (IsLocalRing.closedPoint _) (by
      rw [Scheme.fromSpecResidueField_apply]
      exact hz)
  exact ⟨p, by simp only [Function.comp_apply, hp]⟩

/-- The swap `V ×_Y V ⟶ V ×_Y V`. -/
noncomputable abbrev pairSwap (f : V ⟶ Y) : pullback f f ⟶ pullback f f :=
  pullback.lift (pullback.snd f f) (pullback.fst f f) pullback.condition.symm

/-- A descent cocycle is inverted by the swap. -/
lemma IsDescentCocycle.comp_swap (hc : IsDescentCocycle f c) (z : ↥(pullback f f)) :
    c z ∘ c ((pairSwap f).base z) = id := by
  let L : pullback f f ⟶ tripleProduct f :=
    pullback.lift (𝟙 _) (pairSwap f) (by simp [pairSwap])
  have hL : L ≫ tripleProj₁₃ f = pullback.fst f f ≫ pullback.diagonal f :=
    pullback.hom_ext (by
      rw [Category.assoc, pullback.lift_fst, pullback.lift_fst_assoc, Category.id_comp,
        Category.assoc, pullback.diagonal_fst, Category.comp_id]) (by simp [L, pairSwap])
  have h₁ : L ≫ pullback.fst _ _ = 𝟙 _ := pullback.lift_fst _ _ _
  have h₂ : L ≫ pullback.snd _ _ = pairSwap f := pullback.lift_snd _ _ _
  have := hc.cocycle (L.base z)
  rw [← Scheme.Hom.comp_apply, hL, Scheme.Hom.comp_apply, hc.diagonal, ← Scheme.Hom.comp_apply,
    h₁, ← Scheme.Hom.comp_apply, h₂] at this
  exact this.symm

/-- **Compatibility of orbits with the cocycle**: `orbit (p₁ z) = c z '' orbit (p₂ z)`. -/
lemma orbitAt_fst (hc : IsDescentCocycle f c) (z : ↥(pullback f f)) :
    orbitAt f c s ((pullback.fst f f).base z) =
      c z '' orbitAt f c s ((pullback.snd f f).base z) := by
  have h₁₃ : tripleProj₁₃ f ≫ pullback.fst f f =
      pullback.fst (pullback.snd f f) (pullback.fst f f) ≫ pullback.fst f f :=
    pullback.lift_fst _ _ _
  refine subset_antisymm ?_ ?_
  · rintro _ ⟨z₁, hz₁, rfl⟩
    have hz₁' : (pullback.fst f f).base z₁ = (pullback.fst f f).base z := hz₁
    have hsw : (pullback.snd f f).base ((pairSwap f).base z) = (pullback.fst f f).base z₁ := by
      rw [← Scheme.Hom.comp_apply, pullback.lift_snd, hz₁']
    obtain ⟨τ, h₁, h₂⟩ := Scheme.Pullback.exists_preimage_pullback (f := pullback.snd f f)
      (g := pullback.fst f f) _ _ hsw
    refine ⟨c ((pairSwap f).base z) (c z₁ s), ⟨(tripleProj₁₃ f).base τ, ?_, ?_⟩, ?_⟩
    · change (pullback.fst f f).base ((tripleProj₁₃ f).base τ) = _
      rw [← Scheme.Hom.comp_apply, h₁₃, Scheme.Hom.comp_apply, h₁, ← Scheme.Hom.comp_apply,
        pullback.lift_fst]
    · simp only
      rw [hc.cocycle τ, Function.comp_apply, h₁, h₂]
    · exact congrFun (hc.comp_swap z) _
  · rintro _ ⟨_, ⟨z₁, hz₁, rfl⟩, rfl⟩
    have hz₁' : (pullback.snd f f).base z = (pullback.fst f f).base z₁ := hz₁.symm
    obtain ⟨τ, h₁, h₂⟩ := Scheme.Pullback.exists_preimage_pullback (f := pullback.snd f f)
      (g := pullback.fst f f) _ _ hz₁'
    refine ⟨(tripleProj₁₃ f).base τ, ?_, ?_⟩
    · change (pullback.fst f f).base ((tripleProj₁₃ f).base τ) = _
      rw [← Scheme.Hom.comp_apply, h₁₃, Scheme.Hom.comp_apply, h₁]
    · simp only
      rw [hc.cocycle τ, Function.comp_apply, h₁, h₂]

end Orbit

/-- A locally constant function takes the same value at a point and its generizations. -/
lemma _root_.IsLocallyConstant.apply_eq_of_specializes {X A : Type*} [TopologicalSpace X]
    {g : X → A} (hg : IsLocallyConstant g) {x y : X} (h : x ⤳ y) : g x = g y :=
  h.mem_open (hg.isOpen_fiber (g y)) rfl

/-- **Finite subsheaves from orbits.** Let `f : V ⟶ Y` be flat and quasi-compact, `η` a point
of `Y` specializing to every point, and assume `f` is generically connected relative to `η`
(`AlgebraicGeometry.IsGenericallyConnected`). Then for a descent cocycle `c` on `S_V`, every
`s ∈ S` at a point `v` of `V` lies in a finite subsheaf: a locally constant function `T` from
`V` to finite subsets of `S`, compatible with `c`, with `s ∈ T v`. It is the orbit of `s` at
a generization of the point lying over `η`. -/
theorem exists_finite_invariant_subset_of_isGenericallyConnected (f : V ⟶ Y) [Flat f]
    [QuasiCompact f] {η : Y} (hη : ∀ y, η ⤳ y) (hQ : IsGenericallyConnected f η) {S : Type*}
    {c : ↥(pullback f f) → S → S} (hc : IsDescentCocycle f c) (v : V) (s : S) :
    ∃ T : V → Set S, (∀ v, (T v).Finite) ∧ IsLocallyConstant T ∧
      (∀ z, T ((pullback.fst f f).base z) = c z '' T ((pullback.snd f f).base z)) ∧
        s ∈ T v := by
  have hgen (x : V) : ∃ a, a ⤳ x ∧ f.base a = η := Flat.generalizingMap f (hη (f.base x))
  choose g hg hgη using hgen
  have hopen (A : Set S) (hA : A.Finite) : IsOpen {z | ∀ t ∈ A, c z t = t} := by
    have : {z | ∀ t ∈ A, c z t = t} = ⋂ t ∈ A, (fun z ↦ c z t) ⁻¹' {t} := by
      ext z
      simp
    rw [this]
    exact hA.isOpen_biInter fun t _ ↦ (hc.isLocallyConstant t).isOpen_fiber t
  have hdiag (x : V) (A : Set S) : (pullback.diagonal f).base x ∈ {z | ∀ t ∈ A, c z t = t} :=
    fun t _ ↦ by rw [hc.diagonal]; rfl
  have hfix {A : Set S} {z} (h : z ∈ {z | ∀ t ∈ A, c z t = t}) : c z '' A = A := by
    conv_rhs => rw [← Set.image_id A]
    exact Set.image_congr h
  have hfst (x : V) : (pullback.fst f f).base ((pullback.diagonal f).base x) = x := by
    rw [← Scheme.Hom.comp_apply, pullback.diagonal_fst]
    rfl
  -- generic generizations of a point have the same orbit
  have hkey (x a b : V) (ha : a ⤳ x) (hb : b ⤳ x) (haη : f.base a = η) (hbη : f.base b = η) :
      orbitAt f c s a = orbitAt f c s b := by
    obtain ⟨U, hU, hUp⟩ := hQ x _ (hopen _ (finite_orbitAt s hc b)) (hdiag x _)
    obtain ⟨z, hz, h₁, h₂⟩ := hUp x (mem_of_mem_nhds hU) a b ha hb haη hbη
    rw [← h₁, orbitAt_fst s hc, h₂, hfix hz]
  refine ⟨fun x ↦ orbitAt f c s (g x), fun x ↦ finite_orbitAt s hc _, ?_, fun z ↦ ?_, ?_⟩
  · rw [IsLocallyConstant.iff_eventually_eq]
    intro x
    obtain ⟨U, hU, hUp⟩ := hQ x _ (hopen _ (finite_orbitAt s hc (g x))) (hdiag x _)
    filter_upwards [hU] with x₁ hx₁
    obtain ⟨z, hz, h₁, h₂⟩ := hUp x₁ hx₁ (g x₁) (g x) (hg x₁) (hg x) (hgη x₁) (hgη x)
    rw [← h₁, orbitAt_fst s hc, h₂, hfix hz]
  · obtain ⟨ζ, hζ, hζη⟩ := Flat.generalizingMap (pullback.fst f f ≫ f)
      (hη ((pullback.fst f f ≫ f).base z))
    have h₁ := hζ.map (pullback.fst f f).base.hom.continuous
    have h₂ := hζ.map (pullback.snd f f).base.hom.continuous
    have h₁η : f.base ((pullback.fst f f).base ζ) = η := by
      rw [← Scheme.Hom.comp_apply]
      exact hζη
    have h₂η : f.base ((pullback.snd f f).base ζ) = η := by
      rw [← Scheme.Hom.comp_apply, ← pullback.condition]
      exact hζη
    change orbitAt f c s (g _) = c z '' orbitAt f c s (g _)
    rw [hkey _ _ _ (hg _) h₁ (hgη _) h₁η, hkey _ _ _ (hg _) h₂ (hgη _) h₂η, orbitAt_fst s hc]
    exact Set.image_congr fun t _ ↦ (hc.isLocallyConstant t).apply_eq_of_specializes hζ
  · refine ⟨(pullback.diagonal f).base (g v), hfst _, ?_⟩
    simp only
    rw [hc.diagonal]
    rfl

/-- **Descent of finite subsheaves** along a surjective submersive morphism `j : W ⟶ V`: if the
restriction of a descent cocycle `c` along `j` has finite subsheaves through every point, so
does `c`. Indeed a finite subsheaf `T'` for the restriction is constant on the fibres of `j`,
the restricted cocycle being the identity on `W ×_V W`, so it is the pullback of a function `T`
on `V`, which is locally constant as `j` is submersive. -/
theorem exists_finite_invariant_subset_of_comp (f : V ⟶ Y) {W : Scheme.{u}} (j : W ⟶ V)
    (hj : Function.Surjective j.base)
    (hsub : ∀ E : Set V, IsOpen (j.base ⁻¹' E) → IsOpen E) {S : Type*}
    {c : ↥(pullback f f) → S → S} (hc : IsDescentCocycle f c)
    (H : ∀ (w : W) (s : S), ∃ T : W → Set S, (∀ w, (T w).Finite) ∧ IsLocallyConstant T ∧
      (∀ z, T ((pullback.fst (j ≫ f) (j ≫ f)).base z) =
        restrictCocycle j c z '' T ((pullback.snd (j ≫ f) (j ≫ f)).base z)) ∧ s ∈ T w)
    (v : V) (s : S) :
    ∃ T : V → Set S, (∀ v, (T v).Finite) ∧ IsLocallyConstant T ∧
      (∀ z, T ((pullback.fst f f).base z) = c z '' T ((pullback.snd f f).base z)) ∧
        s ∈ T v := by
  obtain ⟨w, rfl⟩ := hj v
  obtain ⟨T', hfin, hlc, hinv, hs⟩ := H w s
  choose σ hσ using hj
  -- `T'` is constant on the fibres of `j`
  have hfib (w₁ w₂ : W) (h : j.base w₁ = j.base w₂) : T' w₁ = T' w₂ := by
    obtain ⟨ρ, h₁, h₂⟩ := Scheme.Pullback.exists_preimage_pullback (f := j) (g := j) w₁ w₂ h
    let L : pullback j j ⟶ pullback (j ≫ f) (j ≫ f) :=
      pullback.map j j (j ≫ f) (j ≫ f) (𝟙 _) (𝟙 _) f (by simp) (by simp)
    have hL : L ≫ pairRestrict j = pullback.fst j j ≫ j ≫ pullback.diagonal f :=
      pullback.hom_ext (by simp [L]) (by simp [L, pullback.condition])
    have hid : restrictCocycle j c (L.base ρ) = id := by
      change c ((pairRestrict j).base (L.base ρ)) = id
      rw [← Scheme.Hom.comp_apply, hL, Scheme.Hom.comp_apply, Scheme.Hom.comp_apply]
      exact hc.diagonal _
    have e₁ : (pullback.fst (j ≫ f) (j ≫ f)).base (L.base ρ) = w₁ := by
      rw [← Scheme.Hom.comp_apply, pullback.lift_fst, Category.comp_id, h₁]
    have e₂ : (pullback.snd (j ≫ f) (j ≫ f)).base (L.base ρ) = w₂ := by
      rw [← Scheme.Hom.comp_apply, pullback.lift_snd, Category.comp_id, h₂]
    have := hinv (L.base ρ)
    rwa [e₁, e₂, hid, Set.image_id] at this
  have hT (w₁ : W) : T' (σ (j.base w₁)) = T' w₁ := hfib _ _ (hσ _)
  refine ⟨fun x ↦ T' (σ x), fun x ↦ hfin _, fun A ↦ hsub _ ?_, fun z ↦ ?_, ?_⟩
  · have : j.base ⁻¹' ((fun x ↦ T' (σ x)) ⁻¹' A) = T' ⁻¹' A := by
      ext w₁
      simp only [Set.mem_preimage, hT]
    rw [this]
    exact hlc A
  · -- lift `z` to `W ×_Y W`
    obtain ⟨w₁, hw₁⟩ : ∃ w₁, j.base w₁ = (pullback.fst f f).base z := ⟨σ _, hσ _⟩
    obtain ⟨ρ₁, hρ₁, hρ₁'⟩ := Scheme.Pullback.exists_preimage_pullback
      (f := pullback.fst f f) (g := j) z w₁ hw₁.symm
    let q₁ : pullback (pullback.fst f f) j ⟶ V := pullback.fst _ _ ≫ pullback.snd f f
    obtain ⟨w₂, hw₂⟩ : ∃ w₂, j.base w₂ = q₁.base ρ₁ := ⟨σ _, hσ _⟩
    obtain ⟨ρ₂, hρ₂, hρ₂'⟩ := Scheme.Pullback.exists_preimage_pullback (f := q₁) (g := j) ρ₁ w₂
      hw₂.symm
    let M : pullback q₁ j ⟶ pullback (j ≫ f) (j ≫ f) :=
      pullback.lift (pullback.fst _ _ ≫ pullback.snd _ _) (pullback.snd _ _) (by
      calc (pullback.fst q₁ j ≫ pullback.snd (pullback.fst f f) j) ≫ j ≫ f
          _ = pullback.fst q₁ j ≫ (pullback.snd (pullback.fst f f) j ≫ j) ≫ f := by simp
          _ = pullback.fst q₁ j ≫ (pullback.fst (pullback.fst f f) j ≫ pullback.fst f f) ≫ f := by
            rw [pullback.condition]
          _ = pullback.fst q₁ j ≫ q₁ ≫ f := by
            simp only [q₁, Category.assoc]
            rw [pullback.condition (f := f) (g := f)]
          _ = pullback.snd q₁ j ≫ j ≫ f := by rw [pullback.condition_assoc])
    have hM : M ≫ pairRestrict j = pullback.fst _ _ ≫ pullback.fst _ _ := by
      refine pullback.hom_ext ?_ ?_
      · simp only [M, Category.assoc, pullback.lift_fst_assoc, pullback.lift_fst]
        rw [← pullback.condition]
      · simp only [M, Category.assoc, pullback.lift_snd_assoc, pullback.lift_snd]
        rw [← pullback.condition, ← Category.assoc]
    have hz : (pairRestrict j).base (M.base ρ₂) = z := by
      rw [← Scheme.Hom.comp_apply, hM, Scheme.Hom.comp_apply, hρ₂, hρ₁]
    have e₁ : (pullback.fst f f).base z = j.base ((pullback.fst (j ≫ f) (j ≫ f)).base
        (M.base ρ₂)) := by
      rw [← hz, ← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, pullback.lift_fst]
      simp only [Scheme.Hom.comp_apply]
    have e₂ : (pullback.snd f f).base z = j.base ((pullback.snd (j ≫ f) (j ≫ f)).base
        (M.base ρ₂)) := by
      rw [← hz, ← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, pullback.lift_snd]
      simp only [Scheme.Hom.comp_apply]
    simp only
    rw [e₁, e₂, hT, hT, hinv (M.base ρ₂)]
    change c ((pairRestrict j).base (M.base ρ₂)) '' _ = _
    rw [hz]
  · change s ∈ T' (σ (j.base w))
    rwa [hT]

end AlgebraicGeometry
