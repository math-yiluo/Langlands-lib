/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Morphisms.Integral.PointedCover
public import WeilConjectures.SixFunctors.Integral.Exact

/-!
# Restricting germs of a direct image along an integral morphism

Let `f : X ⟶ Y` be an integral morphism, `y` a geometric point of `Y` with algebraically closed
residue field and `t` a geometric point of `X` over `y`. The restriction of germs
`AlgebraicGeometry.Etale.stalkRestrict : (f_* G)_y ⟶ G_t` is surjective
(`AlgebraicGeometry.Etale.surjective_stalkRestrict_of_isIntegralHom`): a germ of `G` at `t` is
a section over a standard étale neighbourhood of `t`, and after shrinking the étale
neighbourhood of `y`, the base change `U ×_Y X` decomposes into pairwise disjoint opens, one of
which maps to this standard étale neighbourhood with `(u, t)` going to the marked point
(`AlgebraicGeometry.Scheme.Hom.Nbhd.exists_pointed_disjoint_cover`). The section extended by
zero on the other opens is a section of `G` over `U ×_Y X` with the given germ.

Consequently `f_*` detects the zero sheaf
(`AlgebraicGeometry.Etale.isZero_of_isZero_lowerStar_obj`) and, being exact, is conservative
(`AlgebraicGeometry.Etale.reflectsIsomorphisms_lowerStar_of_isIntegralHom`).
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite Polynomial

open scoped AlgebraicGeometry.Etale

namespace StandardEtalePair

variable {B Ω : Type*} [CommRing B] [CommRing Ω] (P : StandardEtalePair B)

/-- `P.HasMap α` for the algebra structure given by a ring homomorphism `φ : B →+* Ω`. -/
lemma hasMap_of_eval₂ (φ : B →+* Ω) (α : Ω)
    (h : P.f.eval₂ φ α = 0 ∧ IsUnit (P.g.eval₂ φ α)) :
    letI := φ.toAlgebra; P.HasMap α := by
  let _ := φ.toAlgebra
  exact ⟨by rw [aeval_def]; exact h.1, by rw [aeval_def]; exact h.2⟩

/-- The ring homomorphism `P.Ring →+* Ω` sending `X` to `α`, over a ring homomorphism
`φ : B →+* Ω` with `f(α) = 0` and `g(α)` invertible. -/
noncomputable def liftOfRingHom (φ : B →+* Ω) (α : Ω)
    (h : P.f.eval₂ φ α = 0 ∧ IsUnit (P.g.eval₂ φ α)) : P.Ring →+* Ω :=
  letI := φ.toAlgebra
  (P.lift α (P.hasMap_of_eval₂ φ α h)).toRingHom

lemma liftOfRingHom_comp_algebraMap (φ : B →+* Ω) (α : Ω)
    (h : P.f.eval₂ φ α = 0 ∧ IsUnit (P.g.eval₂ φ α)) :
    (P.liftOfRingHom φ α h).comp (algebraMap B P.Ring) = φ := by
  let _ := φ.toAlgebra
  ext b
  exact (P.lift α (P.hasMap_of_eval₂ φ α h)).commutes b

lemma liftOfRingHom_X (φ : B →+* Ω) (α : Ω)
    (h : P.f.eval₂ φ α = 0 ∧ IsUnit (P.g.eval₂ φ α)) :
    P.liftOfRingHom φ α h P.X = α := by
  let _ := φ.toAlgebra
  exact P.lift_X α (P.hasMap_of_eval₂ φ α h)

/-- A ring homomorphism out of `P.Ring` sends `X` to a root of `f` at which `g` is invertible,
over its restriction to `B`. -/
lemma eval₂_eq_zero_and_isUnit (χ : P.Ring →+* Ω) :
    P.f.eval₂ (χ.comp (algebraMap B P.Ring)) (χ P.X) = 0 ∧
      IsUnit (P.g.eval₂ (χ.comp (algebraMap B P.Ring)) (χ P.X)) := by
  have h : aeval P.X P.f = 0 ∧ IsUnit (aeval P.X P.g) := StandardEtalePair.hasMap_X
  rw [aeval_def, aeval_def] at h
  refine ⟨?_, ?_⟩
  · rw [← hom_eval₂, h.1, map_zero]
  · rw [← hom_eval₂]
    exact h.2.map χ

lemma eq_liftOfRingHom (χ : P.Ring →+* Ω) :
    χ = P.liftOfRingHom _ _ (P.eval₂_eq_zero_and_isUnit χ) := by
  let _ := (χ.comp (algebraMap B P.Ring)).toAlgebra
  let χ' : P.Ring →ₐ[B] Ω := { χ with commutes' := fun _ ↦ rfl }
  have := P.hom_ext (f := χ')
    (g := P.lift (χ P.X) (P.hasMap_of_eval₂ _ _ (P.eval₂_eq_zero_and_isUnit χ)))
    (by rw [P.lift_X]; rfl)
  exact congrArg AlgHom.toRingHom this

lemma eval₂_eq_eval₂_of_coeffs {p : B[X]} {φ₁ φ₂ : B →+* Ω} (h : ∀ b ∈ p.coeffs, φ₁ b = φ₂ b)
    (x : Ω) : p.eval₂ φ₁ x = p.eval₂ φ₂ x := by
  rw [eval₂_eq_sum, eval₂_eq_sum]
  refine Finset.sum_congr rfl fun n hn ↦ ?_
  dsimp only
  rw [h _ (coeff_mem_coeffs (mem_support_iff.mp hn))]

/-- **The values of `liftOfRingHom` depend on finitely many values of `φ`.** -/
lemma exists_finset_liftOfRingHom_eq (α : Ω) (ζ : P.Ring) :
    ∃ S : Finset B, ∀ (φ₁ φ₂ : B →+* Ω) h₁ h₂, (∀ b ∈ S, φ₁ b = φ₂ b) →
      P.liftOfRingHom φ₁ α h₁ ζ = P.liftOfRingHom φ₂ α h₂ ζ := by
  classical
  let T : Subalgebra B P.Ring :=
    { carrier := {ζ | ∃ S : Finset B, ∀ (φ₁ φ₂ : B →+* Ω) h₁ h₂, (∀ b ∈ S, φ₁ b = φ₂ b) →
        P.liftOfRingHom φ₁ α h₁ ζ = P.liftOfRingHom φ₂ α h₂ ζ}
      mul_mem' := by
        rintro a b ⟨S₁, hS₁⟩ ⟨S₂, hS₂⟩
        refine ⟨S₁ ∪ S₂, fun φ₁ φ₂ h₁ h₂ h ↦ ?_⟩
        rw [map_mul, map_mul,
          hS₁ φ₁ φ₂ h₁ h₂ fun b hb ↦ h b (Finset.mem_union_left _ hb),
          hS₂ φ₁ φ₂ h₁ h₂ fun b hb ↦ h b (Finset.mem_union_right _ hb)]
      add_mem' := by
        rintro a b ⟨S₁, hS₁⟩ ⟨S₂, hS₂⟩
        refine ⟨S₁ ∪ S₂, fun φ₁ φ₂ h₁ h₂ h ↦ ?_⟩
        rw [map_add, map_add,
          hS₁ φ₁ φ₂ h₁ h₂ fun b hb ↦ h b (Finset.mem_union_left _ hb),
          hS₂ φ₁ φ₂ h₁ h₂ fun b hb ↦ h b (Finset.mem_union_right _ hb)]
      algebraMap_mem' := by
        intro b
        refine ⟨{b}, fun φ₁ φ₂ h₁ h₂ h ↦ ?_⟩
        rw [← RingHom.comp_apply, liftOfRingHom_comp_algebraMap, ← RingHom.comp_apply,
          liftOfRingHom_comp_algebraMap]
        exact h b (Finset.mem_singleton_self b) }
  have hX : P.X ∈ T := ⟨∅, fun φ₁ φ₂ h₁ h₂ _ ↦ by rw [liftOfRingHom_X, liftOfRingHom_X]⟩
  have hPX := StandardEtalePair.hasMap_X (P := P)
  let u : P.Ring := ((hPX.2.unit⁻¹ : P.Ringˣ) : P.Ring)
  have hu : aeval P.X P.g * u = 1 := hPX.2.mul_val_inv
  have hlu (φ : B →+* Ω) h : P.liftOfRingHom φ α h u * P.g.eval₂ φ α = 1 := by
    have := congrArg (P.liftOfRingHom φ α h) hu
    rw [map_mul, map_one, aeval_def, hom_eval₂, liftOfRingHom_comp_algebraMap,
      liftOfRingHom_X] at this
    rw [mul_comm, this]
  have huT : u ∈ T := by
    refine ⟨P.g.coeffs, fun φ₁ φ₂ h₁ h₂ h ↦ ?_⟩
    have h₁' := hlu φ₁ h₁
    have h₂' := hlu φ₂ h₂
    rw [eval₂_eq_eval₂_of_coeffs h] at h₁'
    calc P.liftOfRingHom φ₁ α h₁ u
        = P.liftOfRingHom φ₁ α h₁ u * (P.g.eval₂ φ₂ α * P.liftOfRingHom φ₂ α h₂ u) := by
          rw [mul_comm (P.g.eval₂ φ₂ α), h₂', mul_one]
      _ = P.liftOfRingHom φ₂ α h₂ u := by rw [← mul_assoc, h₁', one_mul]
  have hT : P.HasMap (⟨P.X, hX⟩ : T) := by
    refine ⟨Subtype.val_injective ?_, IsUnit.of_mul_eq_one ⟨u, huT⟩ (Subtype.val_injective ?_)⟩
    · change T.val (aeval _ P.f) = T.val 0
      rw [← aeval_algHom_apply, map_zero]
      exact hPX.1
    · change T.val (aeval _ P.g * _) = T.val 1
      rw [map_mul, ← aeval_algHom_apply, map_one]
      exact hu
  have hid : T.val.comp (P.lift _ hT) = AlgHom.id B P.Ring := P.hom_ext (by simp)
  have hζ : ζ ∈ T := by
    have := congrArg (fun φ ↦ φ ζ) hid
    simp only [AlgHom.comp_apply, AlgHom.id_apply] at this
    rw [← this]
    exact (P.lift _ hT ζ).2
  exact hζ

/-- The standard étale pair `(X, 1)`, whose algebra is `B` itself. -/
noncomputable def trivialPair (B : Type*) [CommRing B] : StandardEtalePair B where
  f := X
  monic_f := monic_X
  g := 1
  cond := ⟨1, 0, 0, by simp⟩

lemma trivialPair_eval₂ (φ : B →+* Ω) :
    (trivialPair B).f.eval₂ φ 0 = 0 ∧ IsUnit ((trivialPair B).g.eval₂ φ 0) := by
  simp [trivialPair]

end StandardEtalePair

namespace AlgebraicGeometry

open Scheme Scheme.Hom

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [IsIntegralHom f]

/-- Every geometric point `y` of `Y` has a pointed étale neighbourhood `(U, u)` with `U` affine
(an affine open of `Y` containing the image of `y`). -/
lemma Scheme.Hom.Nbhd.exists_isAffine {Ω : Type u} [Field Ω] [IsSepClosed Ω]
    (y : Spec (.of Ω) ⟶ Y) : ∃ c : Nbhd y, IsAffine c.1.left := by
  let c₁ : Nbhd y :=
    Functor.elementsMk _ (Scheme.Etale.mk (𝟙 Y)) (CategoryTheory.Over.homMk y (by simp))
  obtain ⟨U₁, hU₁, hu, -⟩ := exists_isAffineOpen_mem_and_subset (X := c₁.1.left)
    (x := c₁.2.left (default : Spec (.of Ω))) (U := ⊤) trivial
  exact ⟨c₁.restrict U₁ hu, hU₁⟩

variable {f} in
/-- **A germ at a point over `y` extends to a section over a base change `U ×_Y X`.** For an
integral `f`, a geometric point `t` of `X` over a geometric point `y` of `Y` with algebraically
closed residue field and a section `z` of a sheaf `G` over a pointed étale neighbourhood
`(V, v)` of `t`, there are a pointed étale neighbourhood `(U, u)` of `y` and a section of `G`
over `U ×_Y X` whose germ at `(u, t)` is the germ of `z` at `v`. -/
lemma Scheme.Hom.Nbhd.exists_section_toPresheafFiber_eq {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    {y : Spec (.of Ω) ⟶ Y} (t : f.GeometricFiber y) (Λ : Type (u + 1)) [CommRing Λ]
    (G : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) {V : X.Etale}
    (v : (pointSmallEtale t.1).fiber.obj V) (z : ToType (G.obj.obj (op V))) :
    ∃ (c : Nbhd y) (σ : ToType (G.obj.obj (op (f.Etale.obj c.1)))),
      (pointSmallEtale t.1).toPresheafFiber _ ((Etale.baseChangeNbhd f y t).obj c).2 G.obj σ =
        (pointSmallEtale t.1).toPresheafFiber V v G.obj z := by
  classical
  obtain ⟨c₀, hc₀⟩ := Nbhd.exists_isAffine y
  have : IsAffine ((𝟭 Scheme).obj c₀.1.left) := hc₀
  have : IsAffine (pullback c₀.1.hom f) := isAffine_of_isAffineHom (pullback.fst c₀.1.hom f)
  set Z := pullback c₀.1.hom f
  let B := Γ(Z, ⊤)
  -- the étale `Z`-scheme `V ×_X Z` and its point `(v, (u₀, t))`
  let V' := pullback V.hom (pullback.snd c₀.1.hom f)
  let q : V' ⟶ Spec B := pullback.snd V.hom (pullback.snd c₀.1.hom f) ≫ Z.isoSpec.hom
  have hv : v.left ≫ V.hom = t.1 := CategoryTheory.Over.w v
  let w' : Spec (.of Ω) ⟶ V' := pullback.lift v.left (basePt f c₀ t) (by
    rw [hv, basePt_snd])
  -- a standard étale neighbourhood of it, and the lift of `w'` to it
  obtain ⟨P, e, he, x, hx⟩ := AlgebraicGeometry.Etale.exists_standardEtalePair q (w' default)
  have hPet : AlgebraicGeometry.Etale (Spec.map (CommRingCat.ofHom (algebraMap B P.Ring))) :=
    HasRingHomProperty.Spec_iff.mpr
      (RingHom.etale_algebraMap.mpr (inferInstanceAs (Algebra.Etale B P.Ring)))
  have : AlgebraicGeometry.Etale e := by
    have : AlgebraicGeometry.Etale (e ≫ q) := he ▸ hPet
    exact MorphismProperty.of_postcomp (W := @AlgebraicGeometry.Etale)
      (W' := @AlgebraicGeometry.Etale) e q inferInstance this
  obtain ⟨l, hl, -⟩ := exists_fac_of_etale_of_isSepClosed e w' x hx
  let χ₀ : P.Ring →+* Ω := (Spec.preimage l).hom
  have hl' : Spec.map (CommRingCat.ofHom χ₀) = l := Spec.map_preimage l
  let tB (s : f.GeometricFiber y) : B →+* Ω := (basePt f c₀ s).appTopPoint
  have hχ₀ : χ₀.comp (algebraMap B P.Ring) = tB t := by
    have h₁ : Spec.map (CommRingCat.ofHom (χ₀.comp (algebraMap B P.Ring))) =
        Spec.map (CommRingCat.ofHom (tB t)) := by
      rw [CommRingCat.ofHom_comp, Spec.map_comp, hl', ← he, ← Category.assoc, hl,
        ← Scheme.Hom.comp_toSpecΓ]
      simp only [q, w', ← Category.assoc, pullback.lift_snd]
      rfl
    exact congrArg CommRingCat.Hom.hom (Spec.map_injective h₁)
  let α₀ : Ω := χ₀ P.X
  have hα₀ := P.eval₂_eq_zero_and_isUnit χ₀
  rw [hχ₀] at hα₀
  -- the two standard étale pairs, and the assignment of a pair to each geometric point
  let Pj : Bool → StandardEtalePair B := fun j ↦ cond j P (StandardEtalePair.trivialPair B)
  let S₀ : Finset B := P.f.coeffs ∪ P.g.coeffs
  let m (s : f.GeometricFiber y) : Bool := decide (∀ b ∈ S₀, tB s b = tB t b)
  have hmt : m t = true := by simp [m]
  have hmα (s : {s // m s = true}) :
      P.f.eval₂ (tB s.1) α₀ = 0 ∧ IsUnit (P.g.eval₂ (tB s.1) α₀) := by
    have h := of_decide_eq_true s.2
    rw [StandardEtalePair.eval₂_eq_eval₂_of_coeffs (φ₂ := tB t)
        (fun b hb ↦ h b (Finset.mem_union_left _ hb)),
      StandardEtalePair.eval₂_eq_eval₂_of_coeffs (p := P.g) (φ₂ := tB t)
        (fun b hb ↦ h b (Finset.mem_union_right _ hb))]
    exact hα₀
  let χ : ∀ j, {s // m s = j} → ((Pj j).Ring →+* Ω) := fun j ↦
    Bool.rec (motive := fun j ↦ {s // m s = j} → ((Pj j).Ring →+* Ω))
      (fun s ↦ (StandardEtalePair.trivialPair B).liftOfRingHom (tB s.1) 0
        (StandardEtalePair.trivialPair_eval₂ _))
      (fun s ↦ P.liftOfRingHom (tB s.1) α₀ (hmα s)) j
  have hχ : ∀ j s, (χ j s).comp (algebraMap _ _) = (basePt f c₀ s.1).appTopPoint := by
    intro j s
    cases j
    · exact StandardEtalePair.liftOfRingHom_comp_algebraMap _ _ _ _
    · exact StandardEtalePair.liftOfRingHom_comp_algebraMap _ _ _ _
  have hm : ∃ S : Finset B, ∀ s₁ s₂, (∀ b ∈ S,
      (basePt f c₀ s₁).appTopPoint b = (basePt f c₀ s₂).appTopPoint b) → m s₁ = m s₂ := by
    refine ⟨S₀, fun s₁ s₂ h ↦ ?_⟩
    simp only [m]
    exact decide_eq_decide.mpr (forall₂_congr fun b hb ↦ by rw [show tB s₁ b = tB s₂ b from h b hb])
  have hχS : ∀ j (ζ : (Pj j).Ring), ∃ S : Finset B, ∀ s₁ s₂ : {s // m s = j}, (∀ b ∈ S,
      (basePt f c₀ s₁.1).appTopPoint b = (basePt f c₀ s₂.1).appTopPoint b) →
      χ j s₁ ζ = χ j s₂ ζ := by
    intro j
    cases j
    · intro ζ
      obtain ⟨S, hS⟩ := (StandardEtalePair.trivialPair B).exists_finset_liftOfRingHom_eq
        (0 : Ω) ζ
      exact ⟨S, fun s₁ s₂ h ↦ hS _ _ _ _ h⟩
    · intro ζ
      obtain ⟨S, hS⟩ := P.exists_finset_liftOfRingHom_eq α₀ ζ
      exact ⟨S, fun s₁ s₂ h ↦ hS _ _ _ _ h⟩
  obtain ⟨c, h, ι, Q, k, ν, hdisj, hsup, hν, hpt⟩ :=
    Nbhd.exists_pointed_disjoint_cover f c₀ Pj m (Set.toFinite _) χ hχ hm hχS
  -- the geometric point `(u, t)` as a point of the fibre functor at a piece
  let ptQ (l : ι) (p : Spec (.of Ω) ⟶ Q l) (hp : p ≫ (Q l).ι = basePt f c t) :
      (pointSmallEtale t.1).fiber.obj (Nbhd.openObj f c (Q l)) :=
    CategoryTheory.Over.homMk p (by
      change p ≫ (Q l).ι ≫ pullback.snd c.1.hom f = t.1
      rw [← Category.assoc, hp, basePt_snd])
  -- sections over the pieces with the right germ at `(u, t)`
  have ha (l : ι) : ∃ a : ToType (G.obj.obj (op (Nbhd.openObj f c (Q l)))),
      ∀ p hp, (pointSmallEtale t.1).toPresheafFiber _ (ptQ l p hp) G.obj a =
        (pointSmallEtale t.1).toPresheafFiber V v G.obj z := by
    obtain ⟨j, νl, hνl, hptl⟩ : ∃ j, ∃ νl : (Q l).toScheme ⟶ Spec (.of (Pj j).Ring),
        νl ≫ Spec.map (CommRingCat.ofHom (algebraMap _ (Pj j).Ring)) =
          (Q l).ι ≫ (f.Etale.map h.val).left ≫ (pullback c₀.1.hom f).toSpecΓ ∧
        ∀ p : Spec (.of Ω) ⟶ Q l, p ≫ (Q l).ι = basePt f c t →
          ∃ e : m t = j, p ≫ νl = Spec.map (CommRingCat.ofHom (χ j ⟨t, e⟩)) :=
      ⟨k l, ν l, hν l, hpt t l⟩
    cases j
    · refine ⟨0, fun p hp ↦ ?_⟩
      obtain ⟨e, -⟩ := hptl p hp
      exact absurd (hmt.symm.trans e) (by simp)
    · -- the piece maps to `V` through the standard étale neighbourhood
      have hνe : νl ≫ e ≫ pullback.snd V.hom (pullback.snd c₀.1.hom f) =
          (Q l).ι ≫ (f.Etale.map h.val).left := by
        rw [← cancel_mono Z.isoSpec.hom]
        simp only [Category.assoc]
        change νl ≫ e ≫ q = _
        rw [he]
        exact hνl
      let mor : Nbhd.openObj f c (Q l) ⟶ V :=
        MorphismProperty.Over.homMk (νl ≫ e ≫ pullback.fst V.hom (pullback.snd c₀.1.hom f)) (by
          change (νl ≫ e ≫ pullback.fst V.hom (pullback.snd c₀.1.hom f)) ≫ V.hom =
            (Q l).ι ≫ pullback.snd c.1.hom f
          rw [Category.assoc, Category.assoc, pullback.condition, ← Category.assoc e,
            ← Category.assoc νl, hνe, Category.assoc, Hom.etale_map_left_comp_snd])
      refine ⟨G.obj.map mor.op z, fun p hp ↦ ?_⟩
      rw [GrothendieckTopology.Point.toPresheafFiber_w_apply]
      obtain ⟨e', he'⟩ := hptl p hp
      have hχt : χ true ⟨t, e'⟩ = χ₀ := by
        refine ((P.eq_liftOfRingHom χ₀).trans ?_).symm
        change _ = P.liftOfRingHom (tB t) α₀ (hmα ⟨t, e'⟩)
        congr 1
      have hpt' : (pointSmallEtale t.1).fiber.map mor (ptQ l p hp) = v := by
        refine CategoryTheory.Over.OverMorphism.ext ?_
        change p ≫ νl ≫ e ≫ pullback.fst V.hom (pullback.snd c₀.1.hom f) = v.left
        rw [← Category.assoc, he', hχt, hl', ← Category.assoc, hl, pullback.lift_fst]
      rw [hpt']
  choose a ha using ha
  -- glue the sections over the disjoint pieces
  let F := (sheafCompose X.smallEtaleTopology (CategoryTheory.forget (ModuleCat.{u + 1} Λ))).obj G
  let π (l : ι) := Nbhd.openIncl f c (Q l)
  have hcov : Sieve.ofArrows _ π ∈ X.smallEtaleTopology _ := by
    rw [ofArrows_mem_smallEtaleTopology_iff, Set.eq_univ_iff_forall]
    intro w
    have : w ∈ (⨆ l, Q l) := hsup ▸ trivial
    obtain ⟨l, hl⟩ := TopologicalSpace.Opens.mem_iSup.mp this
    refine Set.mem_iUnion.mpr ⟨l, ?_⟩
    change w ∈ Set.range (Q l).ι
    rw [Scheme.Opens.range_ι]
    exact hl
  have hdisj' : ∀ i j, i ≠ j →
      Disjoint (Set.range (π i).left.base) (Set.range (π j).left.base) := by
    intro i j hij
    change Disjoint (Set.range (Q i).ι.base) (Set.range (Q j).ι.base)
    simp only [Scheme.Opens.range_ι]
    rw [Set.disjoint_iff_inter_eq_empty, ← TopologicalSpace.Opens.coe_inf,
      (hdisj i j hij).eq_bot, TopologicalSpace.Opens.coe_bot]
  obtain ⟨b, hb, -⟩ := F.property.existsUnique_amalgamation_ofArrows π hcov (E := PUnit)
    (fun l ↦ TypeCat.ofHom fun _ ↦ a l) (Etale.comp_map_eq_of_disjoint F _ π hdisj' _)
  refine ⟨c, b PUnit.unit, ?_⟩
  -- the germ at `(u, t)` is computed on the piece containing it
  have hmem : basePt f c t default ∈ (⨆ l, Q l) := hsup ▸ trivial
  obtain ⟨l, hl⟩ := TopologicalSpace.Opens.mem_iSup.mp hmem
  have hrange : Set.range (basePt f c t).base ⊆ Set.range (Q l).ι.base := by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨p, rfl⟩
    rw [Subsingleton.elim (α := Spec (.of Ω)) p default]
    exact hl
  let p := IsOpenImmersion.lift (Q l).ι (basePt f c t) hrange
  have hp : p ≫ (Q l).ι = basePt f c t := IsOpenImmersion.lift_fac _ _ _
  have hbl := congrArg (fun φ ↦ φ PUnit.unit) (hb l)
  change G.obj.map (π l).op (b PUnit.unit) = a l at hbl
  have hpt' : (pointSmallEtale t.1).fiber.map (π l) (ptQ l p hp) =
      ((Etale.baseChangeNbhd f y t).obj c).2 := by
    refine CategoryTheory.Over.OverMorphism.ext ?_
    change p ≫ (Q l).ι = basePt f c t
    exact hp
  rw [← ha l p hp, ← hbl, GrothendieckTopology.Point.toPresheafFiber_w_apply, hpt']
  rfl

end AlgebraicGeometry

namespace AlgebraicGeometry

open Scheme Scheme.Hom

variable (Λ : Type (u + 1)) [CommRing Λ] {X Y : Scheme.{u}} (f : X ⟶ Y) [IsIntegralHom f]

/-- **The restriction of germs of a direct image along an integral morphism is surjective**: for
a geometric point `t` of `X` over a geometric point `y` of `Y` with algebraically closed residue
field, every germ of `G` at `t` is the restriction of a germ of `f_* G` at `y`. -/
lemma Etale.surjective_stalkRestrict_of_isIntegralHom {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (y : Spec (.of Ω) ⟶ Y) (t : f.GeometricFiber y)
    (G : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    Function.Surjective (Etale.stalkRestrict (ModuleCat.{u + 1} Λ) f y t G) := by
  have : PreservesFilteredColimitsOfSize.{u, u} (CategoryTheory.forget (ModuleCat.{u + 1} Λ)) :=
    preservesFilteredColimitsOfSize_shrink.{u, u + 1, u, u + 1} _
  intro p
  obtain ⟨V, v, z, rfl⟩ := (pointSmallEtale t.1).toPresheafFiber_jointly_surjective
    (P := G.obj) p
  obtain ⟨c, σ, hσ⟩ := Nbhd.exists_section_toPresheafFiber_eq t Λ G v z
  refine ⟨(pointSmallEtale y).toPresheafFiber c.1 c.2 ((f)_*[ModuleCat.{u + 1} Λ].obj G).obj σ,
    ?_⟩
  rw [← hσ]
  exact ConcreteCategory.congr_hom
    (Etale.toPresheafFiber_stalkRestrict (ModuleCat.{u + 1} Λ) f y t G c) σ

end AlgebraicGeometry
