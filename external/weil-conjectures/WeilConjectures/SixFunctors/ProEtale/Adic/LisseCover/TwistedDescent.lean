/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.Adic.LisseCover.TwistedSheaf
public import WeilConjectures.AlgebraicGeometry.EffectiveDescent.AffineCoaction
public import WeilConjectures.AlgebraicGeometry.FiniteLocallyConstantEtale.Constant
public import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FlatDescent
public import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Finite

/-!
# Affine descent of finite twisted sheaves

Let `f : V ⟶ Y` be weakly étale, `c` a descent cocycle on the constant sheaf with finite fibre
`Fin N`, and `s : S ⟶ Y` an open immersion from an affine scheme, covered by an affine
`p : W ⟶ S` (flat and surjective) mapping to `V` through `j : W ⟶ V`. The trivial cover
`∐_{Fin N} W ⟶ W` carries the coaction transporting the summands along `c`, and affine flat
descent (`AlgebraicGeometry.exists_isPullback_of_coaction`) descends it to a finite étale
`n : N ⟶ S`. Its `S`-morphisms from étale `Y`-schemes over `S` are the sections of the sheaf
of sets defined by `c`
(`AlgebraicGeometry.TwistedDescent.isUniversalSection`, in the sense of
`AlgebraicGeometry.Scheme.IsUniversalSection`).
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry.TwistedDescent

open Scheme

section Index

variable (N : ℕ) (W : Scheme.{u})

/-- The trivial cover `∐_{Fin N} W` of `W`. -/
noncomputable abbrev triv : Scheme.{u} := ∐ fun _ : ULift.{u} (Fin N) ↦ W

/-- The projection `∐_{Fin N} W ⟶ W`. -/
noncomputable abbrev trivπ : triv N W ⟶ W := Sigma.desc fun _ ↦ 𝟙 W

/-- The index of a point of `∐_{Fin N} W`. -/
noncomputable def idx (x : ↥(triv N W)) : Fin N := (sigmaIdx (ULift.{u} (Fin N)) W x).down

variable {N W}

/-- The morphism into the trivial cover given by a locally constant index function. -/
noncomputable def ofIdx {T : Scheme.{u}} (w : T ⟶ W) (φ : C(T, Fin N)) : T ⟶ triv N W :=
  (sigmaHomEquiv (S' := ULift.{u} (Fin N)) (X := W) Equiv.ulift.symm w φ).1

lemma ofIdx_trivπ {T : Scheme.{u}} (w : T ⟶ W) (φ : C(T, Fin N)) :
    ofIdx w φ ≫ trivπ N W = w :=
  (sigmaHomEquiv (S' := ULift.{u} (Fin N)) (X := W) Equiv.ulift.symm w φ).2

lemma idx_ofIdx {T : Scheme.{u}} (w : T ⟶ W) (φ : C(T, Fin N)) (z : T) :
    idx N W ((ofIdx w φ).base z) = φ z := by
  have := congrArg (fun ψ : C(T, Fin N) ↦ ψ z)
    ((sigmaHomEquiv (S' := ULift.{u} (Fin N)) (X := W) Equiv.ulift.symm w).left_inv φ)
  exact this

/-- Morphisms into the trivial cover are determined by their projection and their index. -/
lemma hom_ext_triv {T : Scheme.{u}} {a b : T ⟶ triv N W} (h : a ≫ trivπ N W = b ≫ trivπ N W)
    (hidx : ∀ z, idx N W (a.base z) = idx N W (b.base z)) : a = b := by
  have := (sigmaHomEquiv (S' := ULift.{u} (Fin N)) (X := W) Equiv.ulift.symm
    (b ≫ trivπ N W)).symm.injective (a₁ := ⟨a, h⟩) (a₂ := ⟨b, rfl⟩)
    (ContinuousMap.ext fun z ↦ hidx z)
  exact congrArg Subtype.val this

lemma continuous_idx : Continuous (idx N W) :=
  continuous_uliftDown.comp (sigmaIdx (ULift.{u} (Fin N)) W).continuous

end Index

/-- The inverse of a self-map of a finite set, as a function of the self-map. -/
noncomputable def finInv {N : ℕ} (g : Fin N → Fin N) (a : Fin N) : Fin N :=
  if h : ∃ b, g b = a then h.choose else a

lemma finInv_apply {N : ℕ} {g : Fin N → Fin N} (hg : Function.Injective g) (b : Fin N) :
    finInv g (g b) = b := by
  have h : ∃ b', g b' = g b := ⟨b, rfl⟩
  simp only [finInv, dite_eq_left h]
  exact hg h.choose_spec

lemma apply_finInv {N : ℕ} {g : Fin N → Fin N} (hg : Function.Surjective g) (a : Fin N) :
    g (finInv g a) = a := by
  have h : ∃ b, g b = a := hg a
  simp only [finInv, dite_eq_left h]
  exact h.choose_spec

lemma finInv_id {N : ℕ} (a : Fin N) : finInv id a = a :=
  finInv_apply (g := id) Function.injective_id a

/-- A descent cocycle on a finite set is locally constant as a function to self-maps. -/
lemma _root_.AlgebraicGeometry.IsDescentCocycle.isLocallyConstant_fun {Y V : Scheme.{u}}
    {f : V ⟶ Y} {N : ℕ}
    {c : ↥(pullback f f) → Fin N → Fin N} (hc : IsDescentCocycle f c) :
    IsLocallyConstant c := by
  rw [IsLocallyConstant.iff_eventually_eq]
  intro z₀
  have : ∀ᶠ z in nhds z₀, ∀ a, c z a = c z₀ a :=
    Filter.eventually_all.2 fun a ↦ (IsLocallyConstant.iff_eventually_eq _).1
      (hc.isLocallyConstant a) z₀
  filter_upwards [this] with z hz
  exact funext hz

section Coaction

variable {Y V : Scheme.{u}} {f : V ⟶ Y} {N : ℕ} {c : ↥(pullback f f) → Fin N → Fin N}
  (hc : IsDescentCocycle f c) {S W : Scheme.{u}} {s : S ⟶ Y} {j : W ⟶ V} {p : W ⟶ S}
  (hjp : j ≫ f = p ≫ s)

include hjp in
lemma kappa_w : (pullback.fst (trivπ N W ≫ p) p ≫ trivπ N W) ≫ j ≫ f =
    pullback.snd (trivπ N W ≫ p) p ≫ j ≫ f := by
  rw [hjp, Category.assoc, ← Category.assoc (trivπ N W), pullback.condition_assoc]

/-- The map `(∐_{Fin N} W) ×_S W ⟶ W ×_Y W` to the pairs of points of `W`. -/
noncomputable def kappa : pullback (trivπ N W ≫ p) p ⟶ pullback (j ≫ f) (j ≫ f) :=
  pullback.lift _ _ (kappa_w hjp)

include hc in
lemma continuous_coactIdx : Continuous fun x : ↥(pullback (trivπ N W ≫ p) p) ↦
    finInv (c ((pairRestrict j).base ((kappa hjp).base x)))
      (idx N W ((pullback.fst (trivπ N W ≫ p) p).base x)) := by
  refine IsLocallyConstant.continuous ?_
  exact IsLocallyConstant.comp₂ (f := fun x ↦ c ((pairRestrict j).base ((kappa hjp).base x)))
    (g := fun x ↦ idx N W ((pullback.fst (trivπ N W ≫ p) p).base x))
    ((hc.isLocallyConstant_fun.comp_continuous (pairRestrict j).base.hom.continuous).comp_continuous
      (kappa hjp).base.hom.continuous)
    ((IsLocallyConstant.iff_continuous _).2
      (continuous_idx.comp (pullback.fst (trivπ N W ≫ p) p).base.hom.continuous)) finInv

/-- The coaction `(∐_{Fin N} W) ×_S W ⟶ ∐_{Fin N} W`, transporting the summands along `c`. -/
noncomputable def coact : pullback (trivπ N W ≫ p) p ⟶ triv N W :=
  ofIdx (pullback.snd _ _) ⟨_, continuous_coactIdx hc hjp⟩

lemma coact_trivπ : coact hc hjp ≫ trivπ N W = pullback.snd (trivπ N W ≫ p) p :=
  ofIdx_trivπ _ _

lemma idx_coact (x : ↥(pullback (trivπ N W ≫ p) p)) :
    idx N W ((coact hc hjp).base x) = finInv (c ((pairRestrict j).base ((kappa hjp).base x)))
      (idx N W ((pullback.fst (trivπ N W ≫ p) p).base x)) :=
  idx_ofIdx _ _ x

@[reassoc]
lemma kappa_fst : kappa hjp ≫ pullback.fst (j ≫ f) (j ≫ f) =
    pullback.fst (trivπ N W ≫ p) p ≫ trivπ N W := pullback.lift_fst _ _ _

@[reassoc]
lemma kappa_snd : kappa hjp ≫ pullback.snd (j ≫ f) (j ≫ f) = pullback.snd (trivπ N W ≫ p) p :=
  pullback.lift_snd _ _ _

include hc in
lemma coact_counit : coactionUnit p (trivπ N W) ≫ coact hc hjp = 𝟙 (triv N W) := by
  refine hom_ext_triv ?_ fun x ↦ ?_
  · rw [Category.assoc, coact_trivπ, pullback.lift_snd, Category.id_comp]
  · have hk : coactionUnit p (trivπ N W) ≫ kappa hjp ≫ pairRestrict j =
        trivπ N W ≫ j ≫ pullback.diagonal f := by
      apply pullback.hom_ext
      · simp [kappa_fst_assoc]
      · simp [kappa_snd_assoc]
    rw [Scheme.Hom.comp_apply, idx_coact]
    have e₁ : (pairRestrict j).base ((kappa hjp).base ((coactionUnit p (trivπ N W)).base x)) =
        (pullback.diagonal f).base (j.base ((trivπ N W).base x)) := by
      simp only [← Scheme.Hom.comp_apply, Category.assoc, hk]
    have e₂ : (pullback.fst (trivπ N W ≫ p) p).base ((coactionUnit p (trivπ N W)).base x) = x := by
      rw [← Scheme.Hom.comp_apply, pullback.lift_fst]
      rfl
    rw [e₁, e₂, hc.diagonal, finInv_id]
    rfl

include hc in
lemma coact_coassoc : coactionMap p (trivπ N W) (coact hc hjp) (coact_trivπ hc hjp) ≫
    coact hc hjp = coactionForget p (trivπ N W) ≫ coact hc hjp := by
  set Z := pullback (pullback.snd (trivπ N W ≫ p) p ≫ p) p
  set cM := coactionMap p (trivπ N W) (coact hc hjp) (coact_trivπ hc hjp)
  set cF := coactionForget p (trivπ N W)
  set z₁ := pullback.fst (pullback.snd (trivπ N W ≫ p) p ≫ p) p
  have hcM₁ : cM ≫ pullback.fst _ _ = z₁ ≫ coact hc hjp := by simp [cM, z₁]
  have hcM₂ : cM ≫ pullback.snd _ _ = pullback.snd _ _ := by simp [cM]
  have hcF₁ : cF ≫ pullback.fst _ _ = z₁ ≫ pullback.fst _ _ := by simp [cF, z₁]
  have hcF₂ : cF ≫ pullback.snd _ _ = pullback.snd _ _ := by simp [cF]
  refine hom_ext_triv ?_ fun x ↦ ?_
  · rw [Category.assoc, Category.assoc, coact_trivπ, hcM₂, hcF₂]
  · -- the triple of points `(w₁, w₂, w₃)`
    have hΘ : (z₁ ≫ kappa hjp) ≫ pullback.snd (j ≫ f) (j ≫ f) =
        (cM ≫ kappa hjp) ≫ pullback.fst (j ≫ f) (j ≫ f) := by
      rw [Category.assoc, kappa_snd, Category.assoc, kappa_fst, reassoc_of% hcM₁, coact_trivπ]
    let Θ : Z ⟶ tripleProduct (j ≫ f) := pullback.lift _ _ hΘ
    have hΘ₁₃ : Θ ≫ tripleProj₁₃ (j ≫ f) = cF ≫ kappa hjp := by
      apply pullback.hom_ext
      · rw [Category.assoc, pullback.lift_fst, pullback.lift_fst_assoc, Category.assoc,
          kappa_fst, Category.assoc, kappa_fst, reassoc_of% hcF₁]
      · rw [Category.assoc, pullback.lift_snd, pullback.lift_snd_assoc, Category.assoc,
          kappa_snd, Category.assoc, kappa_snd, hcM₂, hcF₂]
    have hco := hc.restrict.cocycle (Θ.base x)
    have e₁ : Θ ≫ pullback.fst _ _ = z₁ ≫ kappa hjp := pullback.lift_fst _ _ _
    have e₂ : Θ ≫ pullback.snd _ _ = cM ≫ kappa hjp := pullback.lift_snd _ _ _
    simp only [← Scheme.Hom.comp_apply, hΘ₁₃, e₁, e₂, restrictCocycle] at hco
    simp only [Scheme.Hom.comp_apply] at hco
    rw [Scheme.Hom.comp_apply, Scheme.Hom.comp_apply, idx_coact, idx_coact]
    have q₁ : (pullback.fst (trivπ N W ≫ p) p).base (cM.base x) =
        (coact hc hjp).base (z₁.base x) := by
      rw [← Scheme.Hom.comp_apply, hcM₁, Scheme.Hom.comp_apply]
    have q₂ : (pullback.fst (trivπ N W ≫ p) p).base (cF.base x) =
        (pullback.fst (trivπ N W ≫ p) p).base (z₁.base x) := by
      rw [← Scheme.Hom.comp_apply, hcF₁, Scheme.Hom.comp_apply]
    rw [q₁, idx_coact, q₂, hco]
    set A := c ((pairRestrict j).base ((kappa hjp).base (cM.base x)))
    set B := c ((pairRestrict j).base ((kappa hjp).base (z₁.base x)))
    set i := idx N W ((pullback.fst (trivπ N W ≫ p) p).base (z₁.base x))
    have hA := hc.bijective ((pairRestrict j).base ((kappa hjp).base (cM.base x)))
    have hB := hc.bijective ((pairRestrict j).base ((kappa hjp).base (z₁.base x)))
    have hBA : Function.Injective (B ∘ A) := hB.1.comp hA.1
    rw [← finInv_apply hBA (finInv A (finInv B i))]
    rw [Function.comp_apply, apply_finInv (g := A) hA.2, apply_finInv (g := B) hB.2]

section Descended

variable {Nsch : Scheme.{u}} {n : Nsch ⟶ S} {q : triv N W ⟶ Nsch}
  (hq : IsPullback q (trivπ N W) n p) (hγq : coact hc hjp ≫ q = pullback.fst _ _ ≫ q)
  [Mono s] {U : Scheme.{u}} {π : U ⟶ Y} {w : U ⟶ S} (hw : w ≫ s = π)

include hjp hw in
lemma fst_p_eq : pullback.fst (j ≫ f) π ≫ p = pullback.snd (j ≫ f) π ≫ w := by
  rw [← cancel_mono s, Category.assoc, Category.assoc, ← hjp, hw]
  exact pullback.condition

/-- The lift `W ×_Y U ⟶ ∐_{Fin N} W = N ×_S W` of an `S`-morphism `a : U ⟶ N`. -/
noncomputable def descLift (a : U ⟶ Nsch) (ha : a ≫ n = w) : pullback (j ≫ f) π ⟶ triv N W :=
  hq.lift (pullback.snd _ _ ≫ a) (pullback.fst _ _) (by
    rw [Category.assoc, ha, fst_p_eq hjp hw])

lemma descLift_q (a : U ⟶ Nsch) (ha : a ≫ n = w) :
    descLift hjp hq hw a ha ≫ q = pullback.snd _ _ ≫ a := hq.lift_fst _ _ _

lemma descLift_trivπ (a : U ⟶ Nsch) (ha : a ≫ n = w) :
    descLift hjp hq hw a ha ≫ trivπ N W = pullback.fst _ _ := hq.lift_snd _ _ _

include hγq in
/-- The section of the sheaf defined by the restricted cocycle attached to an `S`-morphism
`U ⟶ N`: the index in `N ×_S W = ∐_{Fin N} W`. -/
lemma isTwistedSection_descLift (a : U ⟶ Nsch) (ha : a ≫ n = w) :
    IsTwistedSection (j ≫ f) (restrictCocycle j c) π
      (fun x ↦ idx N W ((descLift hjp hq hw a ha).base x)) := by
  refine ⟨(IsLocallyConstant.iff_continuous _).2
    (continuous_idx.comp (descLift hjp hq hw a ha).base.hom.continuous), fun w' ↦ ?_⟩
  set r₁ := pullback.fst (pullback.snd (j ≫ f) π) (pullback.snd (j ≫ f) π)
  set r₂ := pullback.snd (pullback.snd (j ≫ f) π) (pullback.snd (j ≫ f) π)
  set L := descLift hjp hq hw a ha
  have hL : (r₁ ≫ L) ≫ trivπ N W ≫ p = (r₂ ≫ pullback.fst (j ≫ f) π) ≫ p := by
    have e : r₁ ≫ pullback.snd (j ≫ f) π = r₂ ≫ pullback.snd (j ≫ f) π := pullback.condition
    rw [Category.assoc, reassoc_of% (descLift_trivπ hjp hq hw a ha), Category.assoc,
      fst_p_eq hjp hw, reassoc_of% e]
  let ℓ : pullback (pullback.snd (j ≫ f) π) (pullback.snd (j ≫ f) π) ⟶
      pullback (trivπ N W ≫ p) p := pullback.lift _ _ hL
  have hℓ : ℓ ≫ coact hc hjp = r₂ ≫ L := by
    refine hq.hom_ext ?_ ?_
    · rw [Category.assoc, hγq, pullback.lift_fst_assoc, Category.assoc,
        descLift_q, Category.assoc, descLift_q, ← Category.assoc, ← Category.assoc]
      exact congrArg (· ≫ a) pullback.condition
    · rw [Category.assoc, coact_trivπ, pullback.lift_snd, Category.assoc, descLift_trivπ]
  have hκ : ℓ ≫ kappa hjp = twistedPairMap (j ≫ f) π := by
    apply pullback.hom_ext
    · rw [Category.assoc, kappa_fst, pullback.lift_fst_assoc, Category.assoc, descLift_trivπ,
        pullback.lift_fst]
    · rw [Category.assoc, kappa_snd, pullback.lift_snd, pullback.lift_snd]
  have e := congrArg (fun g ↦ idx N W (g.base w')) hℓ
  simp only [Scheme.Hom.comp_apply, idx_coact] at e
  have e₁ : (pullback.fst (trivπ N W ≫ p) p).base (ℓ.base w') = L.base (r₁.base w') := by
    rw [← Scheme.Hom.comp_apply, pullback.lift_fst, Scheme.Hom.comp_apply]
  have e₂ : (kappa hjp).base (ℓ.base w') = (twistedPairMap (j ≫ f) π).base w' := by
    rw [← Scheme.Hom.comp_apply, hκ]
  rw [e₁, e₂] at e
  change idx N W (L.base (r₁.base w')) =
    c ((pairRestrict j).base ((twistedPairMap (j ≫ f) π).base w')) (idx N W (L.base (r₂.base w')))
  rw [← e, apply_finInv (hc.bijective _).2]
omit [Mono s] in
include hjp hw in
lemma surjective_snd [Surjective p] : Function.Surjective (pullback.snd (j ≫ f) π).base := by
  intro u
  obtain ⟨w₀, hw₀⟩ := p.surjective (w.base u)
  obtain ⟨x, -, hx⟩ := Scheme.Pullback.exists_preimage_pullback (f := j ≫ f) (g := π) w₀ u (by
    rw [hjp, Scheme.Hom.comp_apply, hw₀, ← Scheme.Hom.comp_apply, hw])
  exact ⟨x, hx⟩

omit [Mono s] in
include hjp hw in
lemma epi_snd [Surjective p] [WeaklyEtale (j ≫ f)] [QuasiCompact (j ≫ f)] :
    Epi (pullback.snd (j ≫ f) π) := by
  have : Surjective (pullback.snd (j ≫ f) π) := ⟨surjective_snd hjp hw⟩
  infer_instance

/-- Distinct `S`-morphisms `U ⟶ N` give distinct sections. -/
lemma descLift_injective [Surjective p] [WeaklyEtale (j ≫ f)] [QuasiCompact (j ≫ f)]
    {a b : U ⟶ Nsch} (ha : a ≫ n = w) (hb : b ≫ n = w)
    (h : ∀ x, idx N W ((descLift hjp hq hw a ha).base x) =
      idx N W ((descLift hjp hq hw b hb).base x)) : a = b := by
  have := epi_snd hjp hw (j := j)
  have e : descLift hjp hq hw a ha = descLift hjp hq hw b hb :=
    hom_ext_triv (by rw [descLift_trivπ, descLift_trivπ]) h
  rw [← cancel_epi (pullback.snd (j ≫ f) π), ← descLift_q hjp hq hw a ha,
    ← descLift_q hjp hq hw b hb, e]

include hγq in
/-- Every section comes from an `S`-morphism `U ⟶ N`. -/
lemma exists_descLift [Surjective p] [WeaklyEtale (j ≫ f)] [QuasiCompact (j ≫ f)]
    {τ : ↥(pullback (j ≫ f) π) → Fin N}
    (hτ : IsTwistedSection (j ≫ f) (restrictCocycle j c) π τ) :
    ∃ (a : U ⟶ Nsch) (ha : a ≫ n = w), ∀ x, idx N W ((descLift hjp hq hw a ha).base x) = τ x := by
  have : Surjective (pullback.snd (j ≫ f) π) := ⟨surjective_snd hjp hw⟩
  let Λ : pullback (j ≫ f) π ⟶ triv N W :=
    ofIdx (pullback.fst _ _) ⟨τ, (IsLocallyConstant.iff_continuous _).1 hτ.1⟩
  have hΛv : Λ ≫ trivπ N W = pullback.fst _ _ := ofIdx_trivπ _ _
  have hΛidx (x) : idx N W (Λ.base x) = τ x := idx_ofIdx _ _ x
  -- `Λ ≫ q` is constant on the fibres of `W ×_Y U ⟶ U`
  have key {Z : Scheme.{u}} (g₁ g₂ : Z ⟶ pullback (j ≫ f) π)
      (hg : g₁ ≫ pullback.snd _ _ = g₂ ≫ pullback.snd _ _) : g₁ ≫ Λ ≫ q = g₂ ≫ Λ ≫ q := by
    let k := pullback.lift g₁ g₂ hg
    have hk₁ : k ≫ pullback.fst _ _ = g₁ := pullback.lift_fst _ _ _
    have hk₂ : k ≫ pullback.snd _ _ = g₂ := pullback.lift_snd _ _ _
    have hL : ((k ≫ pullback.fst _ _) ≫ Λ) ≫ trivπ N W ≫ p =
        (k ≫ pullback.snd _ _ ≫ pullback.fst (j ≫ f) π) ≫ p := by
      simp only [Category.assoc]
      rw [reassoc_of% hΛv, fst_p_eq hjp hw]
      exact congrArg (k ≫ ·) (pullback.condition_assoc w)
    let ℓ := pullback.lift _ _ hL
    have hℓ : ℓ ≫ coact hc hjp = k ≫ pullback.snd _ _ ≫ Λ := by
      refine hom_ext_triv ?_ fun z ↦ ?_
      · rw [Category.assoc, coact_trivπ, pullback.lift_snd, Category.assoc, Category.assoc, hΛv]
      · have hκ : ℓ ≫ kappa hjp = k ≫ twistedPairMap (j ≫ f) π := by
          apply pullback.hom_ext
          · rw [Category.assoc, kappa_fst, pullback.lift_fst_assoc, Category.assoc,
              Category.assoc, hΛv, Category.assoc, pullback.lift_fst]
          · rw [Category.assoc, kappa_snd, pullback.lift_snd, Category.assoc, pullback.lift_snd]
        rw [Scheme.Hom.comp_apply, idx_coact]
        have e₁ : (pullback.fst (trivπ N W ≫ p) p).base (ℓ.base z) =
            Λ.base ((pullback.fst (pullback.snd (j ≫ f) π) (pullback.snd (j ≫ f) π)).base
              (k.base z)) := by
          rw [← Scheme.Hom.comp_apply, pullback.lift_fst]
          simp only [Scheme.Hom.comp_apply]
        have e₂ : (kappa hjp).base (ℓ.base z) = (twistedPairMap (j ≫ f) π).base (k.base z) := by
          rw [← Scheme.Hom.comp_apply, hκ, Scheme.Hom.comp_apply]
        rw [e₁, e₂, hΛidx, hτ.2 (k.base z)]
        simp only [restrictCocycle]
        rw [finInv_apply (hc.bijective _).1]
        simp only [Scheme.Hom.comp_apply, hΛidx]
    calc g₁ ≫ Λ ≫ q = (k ≫ pullback.fst _ _) ≫ Λ ≫ q := by rw [hk₁]
      _ = ℓ ≫ pullback.fst _ _ ≫ q := by rw [pullback.lift_fst_assoc]; simp only [Category.assoc]
      _ = ℓ ≫ coact hc hjp ≫ q := by rw [hγq]
      _ = (k ≫ pullback.snd _ _) ≫ Λ ≫ q := by rw [reassoc_of% hℓ, Category.assoc]
      _ = g₂ ≫ Λ ≫ q := by rw [hk₂]
  let a := EffectiveEpi.desc (pullback.snd (j ≫ f) π) (Λ ≫ q) fun g₁ g₂ hg ↦ key g₁ g₂ hg
  have hfac : pullback.snd (j ≫ f) π ≫ a = Λ ≫ q := EffectiveEpi.fac _ _ _
  have := epi_snd hjp hw (j := j)
  have ha : a ≫ n = w := by
    rw [← cancel_epi (pullback.snd (j ≫ f) π), reassoc_of% hfac, hq.w, reassoc_of% hΛv,
      fst_p_eq hjp hw]
  refine ⟨a, ha, fun x ↦ ?_⟩
  have e : descLift hjp hq hw a ha = Λ :=
    hq.hom_ext (by rw [descLift_q, hfac]) (by rw [descLift_trivπ, hΛv])
  rw [e, hΛidx]
end Descended

end Coaction

lemma idx_ι {N : ℕ} {W : Scheme.{u}} (a : Fin N) (x : W) :
    idx N W ((Sigma.ι (fun _ : ULift.{u} (Fin N) ↦ W) ⟨a⟩).base x) = a := by
  simp [idx, sigmaIdx_ι]

variable {Y V : Scheme.{u}} {f : V ⟶ Y} {N : ℕ} {c : ↥(pullback f f) → Fin N → Fin N}

/-- **Affine descent of a finite twisted sheaf.** Let `s : S ⟶ Y` be an open immersion from an
affine scheme, and `p : W ⟶ S` a flat surjection from an affine scheme with a map `j : W ⟶ V`
over `Y`, with `j ≫ f` weakly étale and quasi-compact. Then the restriction to étale
`S`-schemes of the sheaf of sets defined by a descent cocycle `c` on `Fin N` is represented by a
finite étale `n : N ⟶ S`, with a universal section `ξ`, which takes every value at some
point over every point of `W`. -/
theorem exists_isUniversalSection (hc : IsDescentCocycle f c) {S W : Scheme.{u}} (s : S ⟶ Y)
    [IsOpenImmersion s] [IsAffine S] [IsAffine W] (j : W ⟶ V) (p : W ⟶ S) (hjp : j ≫ f = p ≫ s)
    [Flat p] [Surjective p] [WeaklyEtale (j ≫ f)] [QuasiCompact (j ≫ f)] :
    ∃ (Nsch : Scheme.{u}) (n : Nsch ⟶ S) (_ : Etale n) (_ : IsFinite n)
      (ξ : (twistedSectionsPresheaf f c).obj (op (Scheme.Etale.mk (n ≫ s)))),
      Scheme.IsUniversalSection (twistedSectionsPresheaf f c) s (Scheme.Etale.mk (n ≫ s)) n ξ ∧
      ∀ {K : Type u} [Field K] (wk : Spec (.of K) ⟶ W) (a : Fin N),
        ∃ (nk : Spec (.of K) ⟶ Nsch) (h : (wk ≫ j) ≫ f = nk ≫ n ≫ s),
          ξ.1 ((pullback.lift (wk ≫ j) nk h).base (IsLocalRing.closedPoint K)) = a := by
  obtain ⟨Nsch, -, n, q, hq, hγq⟩ := exists_isPullback_of_coaction p (trivπ N W) (coact hc hjp)
    (coact_trivπ hc hjp) (coact_counit hc hjp) (coact_coassoc hc hjp)
  have hpq : (@Surjective ⊓ @Flat ⊓ @QuasiCompact : MorphismProperty Scheme) p :=
    ⟨⟨inferInstance, inferInstance⟩, inferInstance⟩
  have : Etale (trivπ N W) :=
    IsZariskiLocalAtSource.sigmaDesc (P := @Etale) fun _ ↦ inferInstance
  have hn : Etale n :=
    MorphismProperty.of_isPullback_of_descendsAlong (P := @Etale) hq.flip hpq
      (inferInstanceAs (Etale (trivπ N W)))
  have := IsFinite.descendsAlong_surjective_inf_flat_inf_quasicompact
  have hnf : IsFinite n :=
    MorphismProperty.of_isPullback_of_descendsAlong (P := @IsFinite) hq.flip hpq
      (inferInstanceAs (IsFinite (trivπ N W)))
  have hcov {T : Scheme.{u}} {π : T ⟶ Y} {w : T ⟶ S} (hw : w ≫ s = π) :
      ∀ t, ∃ w₀, (j ≫ f).base w₀ = π.base t := by
    intro t
    obtain ⟨w₀, hw₀⟩ := p.surjective (w.base t)
    exact ⟨w₀, by rw [hjp, Scheme.Hom.comp_apply, hw₀, ← Scheme.Hom.comp_apply, hw]⟩
  -- the universal section
  let NE : Y.Etale := Scheme.Etale.mk (n ≫ s)
  obtain ⟨σ₀, hσ₀, hσ₀τ⟩ := IsTwistedSection.exists_restrict_eq hc (hcov (π := NE.hom) rfl)
    (isTwistedSection_descLift hc hjp hq hγq (π := NE.hom) rfl (𝟙 Nsch) (Category.id_comp _))
  let ξ : (twistedSectionsPresheaf f c).obj (op NE) := ⟨σ₀, hσ₀⟩
  -- its pullbacks along `S`-morphisms `a : W' ⟶ N`
  have hrestr (W' : Y.Etale) (w' : W'.left ⟶ S) (hw' : w' ≫ s = W'.hom) (a : W' ⟶ NE)
      (ha : a.left ≫ n = w') (x : ↥(pullback (j ≫ f) W'.hom)) :
      ((twistedSectionsPresheaf f c).map a.op ξ).1 ((pullbackMapLeft j W'.hom).base x) =
        idx N W ((descLift hjp hq hw' a.left ha).base x) := by
    rw [twistedSectionsPresheaf_map_coe, Function.comp_apply, ← Scheme.Hom.comp_apply]
    have e₁ : pullbackMapLeft j W'.hom ≫ pullbackMapRight f a.left (MorphismProperty.Over.w a) =
        pullbackMapRight (j ≫ f) a.left (MorphismProperty.Over.w a) ≫
          pullbackMapLeft j NE.hom := pullback.hom_ext (by simp) (by simp)
    have e₂ : pullbackMapRight (j ≫ f) a.left (MorphismProperty.Over.w a) ≫
        descLift hjp hq (π := NE.hom) rfl (𝟙 Nsch) (Category.id_comp _) =
          descLift hjp hq hw' a.left ha := by
      refine hq.hom_ext ?_ ?_
      · rw [Category.assoc, descLift_q, descLift_q, pullbackMapRight_snd_assoc]
        erw [Category.comp_id]
      · rw [Category.assoc, descLift_trivπ, descLift_trivπ]
        exact pullback.lift_fst _ _ _
    rw [e₁, Scheme.Hom.comp_apply]
    change (σ₀ ∘ (pullbackMapLeft j NE.hom).base) _ = _
    rw [hσ₀τ, ← e₂, Scheme.Hom.comp_apply]
  refine ⟨Nsch, n, hn, hnf, ξ, fun W' w' hw' ↦ ⟨fun a b hab ↦ ?_, fun e ↦ ?_⟩, ?_⟩
  · have hab' := congrArg Subtype.val hab
    have h := descLift_injective hjp hq hw' a.2 b.2 fun x ↦ by
      rw [← hrestr W' w' hw' a.1 a.2 x, ← hrestr W' w' hw' b.1 b.2 x]
      exact congrFun hab' _
    exact Subtype.ext (MorphismProperty.Over.Hom.ext h)
  · obtain ⟨b, hb, hbτ⟩ := exists_descLift hc hjp hq hγq hw' (e.2.restrict (j := j))
    let a : W' ⟶ NE := MorphismProperty.Over.homMk b (by
      change b ≫ n ≫ s = W'.hom
      rw [reassoc_of% hb, hw']) trivial
    exact ⟨⟨a, hb⟩, Subtype.ext (IsTwistedSection.eq_of_restrict_eq (hcov hw')
      ((twistedSectionsPresheaf f c).map a.op ξ).2 e.2
        (funext fun x ↦ (hrestr W' w' hw' a hb x).trans (hbτ x)))⟩
  · intro K _ wk a
    let nk : Spec (.of K) ⟶ Nsch := wk ≫ Sigma.ι (fun _ : ULift.{u} (Fin N) ↦ W) ⟨a⟩ ≫ q
    have hnk : nk ≫ n = wk ≫ p := by
      simp only [nk, Category.assoc, hq.w, Sigma.ι_comp_desc_assoc, Category.id_comp]
    have h : (wk ≫ j) ≫ f = nk ≫ n ≫ s := by rw [reassoc_of% hnk, Category.assoc, hjp]
    refine ⟨nk, h, ?_⟩
    have hl : pullback.lift (f := f) (g := NE.hom) (wk ≫ j) nk h =
        pullback.lift (f := j ≫ f) (g := NE.hom) wk nk (by rw [← Category.assoc]; exact h) ≫
          pullbackMapLeft j NE.hom := pullback.hom_ext (by simp) (by simp)
    have hd : pullback.lift (f := j ≫ f) (g := NE.hom) wk nk (by rw [← Category.assoc]; exact h) ≫
        descLift hjp hq (π := NE.hom) rfl (𝟙 Nsch) (Category.id_comp _) =
          wk ≫ Sigma.ι (fun _ : ULift.{u} (Fin N) ↦ W) ⟨a⟩ := by
      refine hq.hom_ext ?_ ?_
      · rw [Category.assoc, descLift_q, pullback.lift_snd_assoc]
        erw [Category.comp_id]
      · rw [Category.assoc, descLift_trivπ, pullback.lift_fst, Category.assoc,
          Sigma.ι_comp_desc, Category.comp_id]
    change σ₀ ((pullback.lift (f := f) (g := NE.hom) (wk ≫ j) nk h).base _) = a
    rw [hl, Scheme.Hom.comp_apply]
    change (σ₀ ∘ (pullbackMapLeft j NE.hom).base) _ = _
    rw [hσ₀τ]
    dsimp only
    rw [← Scheme.Hom.comp_apply, hd, Scheme.Hom.comp_apply, idx_ι]

end AlgebraicGeometry.TwistedDescent
