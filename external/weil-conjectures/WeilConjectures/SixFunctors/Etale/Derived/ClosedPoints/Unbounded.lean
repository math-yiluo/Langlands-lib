/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.ClosedPoints.Hypercohomology
public import WeilConjectures.Algebra.Homology.DerivedCategory.TowerLimitRange
public import WeilConjectures.CategoryTheory.DerivedCategory.Products
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.KInjective
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.MapDerivedCategory
public import WeilConjectures.SixFunctors.Etale.Derived.ClosedPoints.Detection
public import WeilConjectures.SixFunctors.Etale.Derived.ClosedPoints.Acyclic
public import WeilConjectures.SixFunctors.Etale.LowerShriek.EtaleMapProjection
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.GlobalSections
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Stalk
public import WeilConjectures.AlgebraicGeometry.GeometricStalkSupport
public import WeilConjectures.CategoryTheory.Triangulated.HomotopyLimit.Basic

/-!
# Cohomology of unbounded complexes with acyclic cohomology sheaves

Let `X` be a scheme, `K ∈ D(X_ét, Λ)` unbounded, and `B` a class of étale `X`-schemes covering
`X_ét` such that `Hᵖ(U, ℋᵠ(K)) = 0` for `p > 0` and `U ∈ B`. Then `Hᵠ(U, K) ≅ Γ(U, ℋᵠ(K))`
for `U ∈ B` (blueprint `lem-kun-0bkz`, Stacks 0BKZ). Following Stacks, `K` is compared with the
homotopy limit `R lim τ^{≥ -n} K` of its truncations: `RΓ(U, -)` preserves countable products,
hence homotopy limits, the towers `Hᵐ(U, τ^{≥ -n} K)` are eventually constant (so the Milnor
sequence has no `lim¹` term), and since `B` covers `X_ét`, an object with vanishing `Hᵠ(U, -)`
for all `U ∈ B` has `ℋᵠ = 0`. As an application, for `X` of finite type over a separably closed
field, an unbounded `Q` whose cohomology sheaves are supported at closed points vanishes if and
only if `Hⁱ(X_ét, Q) = 0` for all `i` (blueprint `corollary-open-direct-image-over-field--2`, Stacks
0F1G).

## Main statements

- `DerivedCategory.isIso_homologyFunctor_map_π_of_isHomotopyLimit_of_isIso`: the Milnor
  sequence for an essentially constant tower in `D(R)`.
- `CategoryTheory.Functor.preservesLimitsOfShape_discrete_nat_rightDerivedFunctor`: unbounded
  right derived functors to `D(R)` preserve countable products.
- `CategoryTheory.Functor.nonempty_homology_rightDerivedFunctor_obj_iso_of_acyclic_of_detects`:
  the abstract form of Stacks 0BKZ.
- `AlgebraicGeometry.Etale.nonempty_homology_rightDerivedFunctor_sheafSections_obj_iso_of_acyclic`
  (`lem-kun-0bkz`).
- `AlgebraicGeometry.Etale.isZero_iff_forall_isZero_homology_rightDerivedGlobalSections`
  (`corollary-open-direct-image-over-field--2`).
-/

@[expose] public section

universe v u

open CategoryTheory Category Limits Opposite Pretriangulated

namespace CategoryTheory.Functor

variable {𝒞 : Type*} [Category 𝒞]

/-- If the successor transitions `G (k + 1) ⟶ G k` of a tower are isomorphisms for `k ≥ n₀`,
then so are all transitions `G b ⟶ G a` for `n₀ ≤ a ≤ b`. -/
lemma isIso_map_homOfLE_op_of_isIso_succ (G : ℕᵒᵖ ⥤ 𝒞) (n₀ : ℕ)
    (hG : ∀ k : ℕ, n₀ ≤ k → IsIso (G.map (homOfLE k.le_succ).op)) {a b : ℕ} (hab : a ≤ b)
    (ha : n₀ ≤ a) : IsIso (G.map (homOfLE hab).op) := by
  induction b, hab using Nat.le_induction with
  | base =>
    have : IsIso (homOfLE (le_refl a)).op := inferInstanceAs (IsIso (𝟙 (op a)))
    infer_instance
  | succ b hab ih =>
    have := hG b (ha.trans hab)
    have e : (homOfLE (hab.trans b.le_succ)).op =
        (homOfLE b.le_succ).op ≫ (homOfLE hab).op := rfl
    rw [e, G.map_comp]
    infer_instance

end CategoryTheory.Functor

namespace DerivedCategory

variable {R : Type v} [Ring R] [HasDerivedCategory (ModuleCat.{v} R)]
  [Abelian.HasKInjectiveResolutions (ModuleCat.{v} R)]

/-- **Milnor sequence for an essentially constant tower.** Let `c` be a homotopy limit cone over
a tower `F` in `D(R)` whose transitions are isomorphisms on `Hᵐ` and on `H^{m-1}`. Then all
legs of `c` are isomorphisms on `Hᵐ`: in the Milnor triangle, `1 - t` is surjective on
`H^{m-1}(∏ Fₙ)`, so that `Hᵐ(c.pt)` is the kernel of `1 - t` on `Hᵐ(∏ Fₙ)`, that is, the
inverse limit of the constant tower `Hᵐ(Fₙ)`. -/
theorem isIso_homologyFunctor_map_π_of_isHomotopyLimit_of_isIso
    {F : ℕᵒᵖ ⥤ DerivedCategory (ModuleCat.{v} R)} {c : Cone F} (hc : IsHomotopyLimit c) (m : ℤ)
    (h₀ : ∀ (a b : ℕ) (hab : a ≤ b),
      IsIso ((homologyFunctor (ModuleCat.{v} R) m).map (F.map (homOfLE hab).op)))
    (h₁ : ∀ (a b : ℕ) (hab : a ≤ b),
      IsIso ((homologyFunctor (ModuleCat.{v} R) (m - 1)).map (F.map (homOfLE hab).op)))
    (n : ℕ) : IsIso ((homologyFunctor (ModuleCat.{v} R) m).map (c.π.app (op n))) := by
  let P := Fan.mk (∏ᶜ fun n : ℕ ↦ F.obj (op n)) (Pi.π fun n : ℕ ↦ F.obj (op n))
  let hP : IsLimit P := productIsProduct _
  obtain ⟨δ, hT⟩ := hc.exists_distTriang hP
  let H := homologyFunctor (ModuleCat.{v} R) m
  let H' := homologyFunctor (ModuleCat.{v} R) (m - 1)
  let hPH : IsLimit (Fan.mk (H.obj P.pt) fun n ↦ H.map (P.proj n)) :=
    isLimitFanMkObjOfIsLimit H _ _ hP
  let hPH' : IsLimit (Fan.mk (H'.obj P.pt) fun n ↦ H'.map (P.proj n)) :=
    isLimitFanMkObjOfIsLimit H' _ _ hP
  -- `1 - t` is surjective on `H^{m-1}(∏ Fₙ)`
  have hepi : Epi (H'.map (𝟙 P.pt - towerShift hP)) := by
    rw [H'.map_sub, H'.map_id]
    refine ModuleCat.epi_one_sub_of_epi (F := F ⋙ H') hPH' _ (fun k ↦ ?_) fun k ↦ ?_
    · dsimp only [Fan.mk, Fan.proj, Functor.comp_map, Discrete.natTrans_app]
      rw [← H'.map_comp, ← H'.map_comp]
      exact congrArg H'.map (towerShift_proj hP k)
    · have := h₁ k (k + 1) k.le_succ
      dsimp only [Functor.comp_map]
      infer_instance
  have hδ := (HomologySequence.epi_homologyMap_mor₂_iff _ hT (m - 1) m (by lia)).1 hepi
  have hmono : Mono (H.map (Fan.IsLimit.lift hP fun n ↦ c.π.app (op n))) :=
    (HomologySequence.mono_homologyMap_mor₁_iff _ hT (m - 1) m (by lia)).2 hδ
  have hex := (ShortComplex.moduleCat_exact_iff _).1 (HomologySequence.exact₂ _ hT m)
  have hz : H.map (Fan.IsLimit.lift hP fun n ↦ c.π.app (op n)) ≫
      H.map (𝟙 P.pt - towerShift hP) = 0 :=
    (H.map_comp _ _).symm.trans ((congrArg H.map (comp_distTriang_mor_zero₁₂ _ hT)).trans
      (H.map_zero _ _))
  have hsub (y : H.obj P.pt) : H.map (𝟙 P.pt - towerShift hP) y = y - H.map (towerShift hP) y := by
    rw [H.map_sub, H.map_id]
    rfl
  -- notation for the tower `Hᵐ(Fₙ)`
  let A (k : ℕ) := H.obj (F.obj (op k))
  let pr (k : ℕ) : H.obj P.pt ⟶ A k := H.map (P.proj k)
  let f (k : ℕ) : A (k + 1) ⟶ A k := H.map (F.map (homOfLE k.le_succ).op)
  have hext (y y' : H.obj P.pt) (h : ∀ k, pr k y = pr k y') : y = y' :=
    ModuleCat.ext_of_isLimit_fan hPH h
  have hf (k : ℕ) : Function.Bijective (f k).hom := by
    have := h₀ k (k + 1) k.le_succ
    exact (ConcreteCategory.isIso_iff_bijective (f k)).1 inferInstance
  have htm (k : ℕ) : H.map (towerShift hP) ≫ pr k = pr (k + 1) ≫ f k := by
    simp only [pr, f, ← H.map_comp, towerShift_proj]
  have ht (k : ℕ) (y : H.obj P.pt) : pr k (H.map (towerShift hP) y) = f k (pr (k + 1) y) := by
    have := ConcreteCategory.congr_hom (htm k) y
    rwa [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply] at this
  have hliftm (k : ℕ) :
      H.map (Fan.IsLimit.lift hP fun n ↦ c.π.app (op n)) ≫ pr k = H.map (c.π.app (op k)) := by
    simp only [pr, ← H.map_comp, Fan.IsLimit.fac]
  have hlift (k : ℕ) (x : H.obj c.pt) :
      pr k (H.map (Fan.IsLimit.lift hP fun n ↦ c.π.app (op n)) x) =
        H.map (c.π.app (op k)) x := by
    have := ConcreteCategory.congr_hom (hliftm k) x
    rwa [ConcreteCategory.comp_apply] at this
  -- elements of the kernel of `1 - t` are determined by any of their components
  have hker (y : H.obj P.pt) (hy : H.map (𝟙 P.pt - towerShift hP) y = 0) (k : ℕ) :
      pr k y = f k (pr (k + 1) y) := by
    rw [← ht]
    rw [hsub, sub_eq_zero] at hy
    exact congrArg (pr k) hy
  rw [ConcreteCategory.isIso_iff_bijective]
  refine ⟨(injective_iff_map_eq_zero _).2 fun x₀ hxx' ↦ ?_, fun z ↦ ?_⟩
  · let y := H.map (Fan.IsLimit.lift hP fun n ↦ c.π.app (op n)) x₀
    have hy : H.map (𝟙 P.pt - towerShift hP) y = 0 := by
      have := ConcreteCategory.congr_hom hz x₀
      rwa [ConcreteCategory.comp_apply] at this
    have hk (k : ℕ) : pr k y = 0 ↔ pr (k + 1) y = 0 := by
      rw [hker y hy k]
      exact ⟨fun h ↦ (hf k).1 (h.trans (map_zero _).symm), fun h ↦ by rw [h, map_zero]⟩
    have h0 (k : ℕ) : pr k y = 0 ↔ pr 0 y = 0 := by
      induction k with
      | zero => rfl
      | succ k ih => rw [← hk, ih]
    have hy0 : y = 0 := hext _ _ fun k ↦ by
      rw [map_zero]
      exact (h0 k).2 ((h0 n).1 (by rw [hlift]; exact hxx'))
    exact (ModuleCat.mono_iff_injective _).1 hmono (hy0.trans (map_zero _).symm)
  · let g (k : ℕ) : A k ⟶ A 0 := H.map (F.map (homOfLE (Nat.zero_le k)).op)
    have hg (k : ℕ) : Function.Bijective (g k).hom := by
      have := h₀ 0 k (Nat.zero_le k)
      exact (ConcreteCategory.isIso_iff_bijective (g k)).1 inferInstance
    have hgf (k : ℕ) (a : A (k + 1)) : g k (f k a) = g (k + 1) a := by
      have e : (homOfLE (Nat.zero_le (k + 1))).op =
          (homOfLE k.le_succ).op ≫ (homOfLE (Nat.zero_le k)).op := rfl
      simp only [g, f, e, F.map_comp, H.map_comp, ModuleCat.hom_comp, LinearMap.comp_apply]
      rfl
    let w := g n z
    let y (k : ℕ) : A k := (Function.surjInv (hg k).2) w
    have hgy (k : ℕ) : g k (y k) = w := Function.surjInv_eq (hg k).2 w
    obtain ⟨Y, hY⟩ := ModuleCat.exists_proj_eq_of_isLimit_fan hPH y
    have hYk (k : ℕ) : pr k Y = y k := hY k
    have hYker : H.map (𝟙 P.pt - towerShift hP) Y = 0 := by
      rw [hsub, sub_eq_zero]
      refine hext _ _ fun k ↦ ?_
      rw [ht, hYk, hYk]
      exact (hg k).1 (by rw [hgf, hgy, hgy])
    obtain ⟨x, hx⟩ := hex Y hYker
    refine ⟨x, ?_⟩
    rw [← hlift]
    exact ((congrArg (pr n) hx).trans (hYk n)).trans ((hg n).1 (by rw [hgy]))

end DerivedCategory

namespace DerivedCategory

variable {C : Type*} [Category C] [Abelian C] [HasDerivedCategory C]

/-- The tower `n ↦ τ^{≥ -n} K` of the truncations of an object `K` of `D(C)`. -/
noncomputable def truncGEOpSequence (K : DerivedCategory C) : ℕᵒᵖ ⥤ DerivedCategory C :=
  Functor.ofOpSequence (X := fun n : ℕ ↦ (TStructure.t.truncGE (-(n : ℤ))).obj K)
    fun n ↦ (TStructure.t.natTransTruncGEOfLE (-((n + 1 : ℕ) : ℤ)) (-(n : ℤ)) (by lia)).app K

instance (K : DerivedCategory C) (n : ℕ) : ((truncGEOpSequence K).obj (op n)).IsGE (-(n : ℤ)) :=
  inferInstanceAs (((TStructure.t.truncGE (-(n : ℤ))).obj K).IsGE (-(n : ℤ)))

/-- The cone over the tower `n ↦ τ^{≥ -n} K` with point `K` given by the truncation maps. -/
noncomputable def truncGEOpSequenceCone (K : DerivedCategory C) : Cone (truncGEOpSequence K) :=
  Cone.mk K (NatTrans.ofOpSequence (fun n ↦ (TStructure.t.truncGEπ (-(n : ℤ))).app K)
    fun n ↦ by
      dsimp [truncGEOpSequence]
      rw [id_comp, Functor.ofOpSequence_map_homOfLE_succ, TStructure.t.π_natTransTruncGEOfLE_app])

@[simp]
lemma truncGEOpSequenceCone_π_app (K : DerivedCategory C) (n : ℕ) :
    (truncGEOpSequenceCone K).π.app (op n) = (TStructure.t.truncGEπ (-(n : ℤ))).app K :=
  rfl

lemma truncGEOpSequence_map_succ (K : DerivedCategory C) (n : ℕ) :
    (truncGEOpSequence K).map (homOfLE n.le_succ).op =
      (TStructure.t.natTransTruncGEOfLE (-((n + 1 : ℕ) : ℤ)) (-(n : ℤ)) (by lia)).app K :=
  Functor.ofOpSequence_map_homOfLE_succ _ n

end DerivedCategory

namespace CategoryTheory.Functor

section Products

variable {C : Type*} [Category C] [Abelian C] [HasDerivedCategory C]
  [Abelian.HasKInjectiveResolutions C] [HasLimitsOfShape (Discrete ℕ) C]
  {R : Type v} [Ring R] [HasDerivedCategory (ModuleCat.{v} R)]
  [Abelian.HasKInjectiveResolutions (ModuleCat.{v} R)]

/-- The unbounded right derived functor of an additive functor `F : C ⥤ ModuleCat R` preserving
countable products preserves countable products: it is computed by applying `F` termwise to
K-injective complexes, these are closed under products, and products of complexes of modules are
products in `D(R)` since products of modules are exact. -/
lemma preservesLimitsOfShape_discrete_nat_rightDerivedFunctor (F : C ⥤ ModuleCat.{v} R)
    [F.Additive] [PreservesLimitsOfShape (Discrete ℕ) F] :
    PreservesLimitsOfShape (Discrete ℕ) F.rightDerivedFunctor := by
  let G := F.mapHomologicalComplex (ComplexShape.up ℤ)
  let q := HomotopyCategory.quotient C (ComplexShape.up ℤ)
  let a : G ⋙ DerivedCategory.Q ≅
      q ⋙ (F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh) :=
    Functor.isoWhiskerLeft G (DerivedCategory.quotientCompQhIso (ModuleCat.{v} R)).symm ≪≫
      (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (F.mapHomotopyCategoryFactors _).symm DerivedCategory.Qh ≪≫
      Functor.associator _ _ _
  let β : G ⋙ DerivedCategory.Q ⟶ DerivedCategory.Q ⋙ F.rightDerivedFunctor :=
    a.hom ≫ Functor.whiskerLeft q F.rightDerivedFunctorUnit ≫
      (Functor.associator _ _ _).inv ≫
      (Functor.isoWhiskerRight (DerivedCategory.quotientCompQhIso C) F.rightDerivedFunctor).hom
  have hβ (I : CochainComplex C ℤ) [I.IsKInjective] : IsIso (β.app I) := by
    dsimp [β, a]
    infer_instance
  have hfamily (K : ℕ → DerivedCategory C) :
      PreservesLimit (Discrete.functor K) F.rightDerivedFunctor := by
    choose I hI e using fun n ↦ DerivedCategory.exists_iso_Q_obj_of_isKInjective (K n)
    have : ∀ n, (I n).IsKInjective := hI
    have : ∀ n, IsIso (β.app (I n)) := fun n ↦ hβ (I n)
    have : (∏ᶜ I).IsKInjective := CochainComplex.isKInjective_of_isLimitFan (productIsProduct I)
    have : IsIso (β.app (∏ᶜ I)) := hβ _
    have hQ := DerivedCategory.isLimitFanMkQObjOfIsKInjective (productIsProduct I)
    let hK : IsLimit (Fan.mk (DerivedCategory.Q.obj (∏ᶜ I))
        fun n ↦ DerivedCategory.Q.map (Pi.π I n) ≫ (e n).some.inv) :=
      Fan.IsLimit.ofIsos hQ (fun n ↦ (e n).some) (Iso.refl _) fun n ↦ by simp
    have hG : IsLimit (Fan.mk (G.obj (∏ᶜ I)) fun n ↦ G.map (Pi.π I n)) :=
      isLimitFanMkObjOfIsLimit G _ _ (productIsProduct I)
    have hQG := DerivedCategory.isLimitFanMkQObj hG
    have hR : IsLimit (Fan.mk (F.rightDerivedFunctor.obj (DerivedCategory.Q.obj (∏ᶜ I)))
        fun n ↦ F.rightDerivedFunctor.map (DerivedCategory.Q.map (Pi.π I n) ≫ (e n).some.inv)) :=
      Fan.IsLimit.ofIsos hQG
        (fun n ↦ F.rightDerivedFunctor.mapIso (e n).some ≪≫ (asIso (β.app (I n))).symm)
        (asIso (β.app (∏ᶜ I))).symm fun n ↦ by
          have hn := β.naturality (Pi.π I n)
          dsimp at hn ⊢
          rw [IsIso.inv_comp_eq, ← F.rightDerivedFunctor.map_comp_assoc, assoc, Iso.inv_hom_id,
            comp_id, ← reassoc_of% hn, IsIso.hom_inv_id, comp_id]
    exact preservesLimit_of_preserves_limit_cone hK ((isLimitMapConeFanMkEquiv _ _ _).symm hR)
  exact preservesLimitsOfShape_of_discrete _

end Products

section Truncation

variable {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
  [HasDerivedCategory C] [HasDerivedCategory D]
  (F : C ⥤ D) [F.Additive] [EnoughInjectives C] [Abelian.HasKInjectiveResolutions C]

omit [EnoughInjectives C] in
/-- Let `K ∈ D(C)` with `H^{-n-1}(K)` acyclic for the left exact functor `F`. Then the
transition `τ^{≥ -n-1} K ⟶ τ^{≥ -n} K` induces isomorphisms on `Hᵐ(RF(-))` for `m ≥ -n`: its
fiber is `H^{-n-1}(K)` placed in degree `-n-1`, whose image under `RF` is concentrated in degree
`-n-1`. -/
lemma isIso_homology_rightDerivedFunctor_map_truncGEOpSequence_map_succ [PreservesFiniteLimits F]
    (K : DerivedCategory C) (n : ℕ)
    (hK : F.IsRightAcyclic ((DerivedCategory.homologyFunctor C (-(n : ℤ) - 1)).obj K))
    (m : ℤ) (hm : -(n : ℤ) ≤ m) :
    IsIso ((DerivedCategory.homologyFunctor D m).map
      (F.rightDerivedFunctor.map
        ((DerivedCategory.truncGEOpSequence K).map (homOfLE n.le_succ).op))) := by
  let t := DerivedCategory.TStructure.t (C := C)
  let RF := F.rightDerivedFunctor
  let L := (DerivedCategory.truncGEOpSequence K).obj (op (n + 1))
  let g := (DerivedCategory.truncGEOpSequence K).map (homOfLE n.le_succ).op
  have hg : g = (t.natTransTruncGEOfLE (-((n + 1 : ℕ) : ℤ)) (-(n : ℤ)) (by lia)).app K :=
    DerivedCategory.truncGEOpSequence_map_succ K n
  let T := (t.triangleLTGE (-(n : ℤ))).obj L
  have hT : T ∈ distTriang _ := t.triangleLTGE_distinguished (-(n : ℤ)) L
  have hRT := RF.map_distinguished T hT
  -- `T.obj₁ = τ^{< -n} L` is `H^{-n-1}(K)` placed in degree `-n-1`
  have : L.IsGE (-((n + 1 : ℕ) : ℤ)) := inferInstance
  have h₁ : T.obj₁.IsGE (-(n : ℤ) - 1 + 1 - (1 : ℕ)) := by
    have : ((t.truncLT (-(n : ℤ))).obj L).IsGE (-((n + 1 : ℕ) : ℤ)) := inferInstance
    exact t.isGE_of_ge ((t.truncLT (-(n : ℤ))).obj L) _ (-((n + 1 : ℕ) : ℤ)) (by lia)
  have h₂ : T.obj₁.IsLE (-(n : ℤ) - 1) := t.isLE_of_le _ (-(n : ℤ) - 1) (-(n : ℤ) - 1) le_rfl
  have hac (q : ℤ) : F.IsRightAcyclic ((DerivedCategory.homologyFunctor C q).obj T.obj₁) := by
    rcases lt_trichotomy q (-(n : ℤ) - 1) with hq | rfl | hq
    · exact IsRightAcyclic.of_isZero (DerivedCategory.isZero_of_isGE _ _ q (by lia) (hX := h₁))
    · have : IsIso ((DerivedCategory.homologyFunctor C (-(n : ℤ) - 1)).map T.mor₁) :=
        DerivedCategory.isIso_homologyFunctor_map_truncLTι_app L (-(n : ℤ)) _ (by lia)
      have : IsIso ((DerivedCategory.homologyFunctor C (-(n : ℤ) - 1)).map
          ((DerivedCategory.truncGEOpSequenceCone K).π.app (op (n + 1)))) :=
        DerivedCategory.isIso_homologyFunctor_map_truncGEπ_app K _ _ (by lia)
      exact hK.of_iso (asIso ((DerivedCategory.homologyFunctor C _).map T.mor₁) ≪≫
        (asIso ((DerivedCategory.homologyFunctor C (-(n : ℤ) - 1)).map
          ((DerivedCategory.truncGEOpSequenceCone K).π.app (op (n + 1))))).symm)
    · exact IsRightAcyclic.of_isZero (DerivedCategory.isZero_of_isLE _ _ q hq (hX := h₂))
  have hz := F.isZero_homology_rightDerivedFunctor_obj_of_isLE 1 T.obj₁ (-(n : ℤ) - 1) h₁ h₂ hac
  -- `RF(τ^{≥ -n} L ⟵ L)` is an isomorphism on `Hᵐ`
  have hiso₁ : IsIso ((DerivedCategory.homologyFunctor D m).map (RF.map T.mor₂)) := by
    have hmono : Mono ((DerivedCategory.homologyFunctor D m).map (RF.map T.mor₂)) :=
      (DerivedCategory.HomologySequence.mono_homologyMap_mor₂_iff _ hRT m).2
        ((hz m (by lia)).eq_of_src _ _)
    have hepi : Epi ((DerivedCategory.homologyFunctor D m).map (RF.map T.mor₂)) :=
      (DerivedCategory.HomologySequence.epi_homologyMap_mor₂_iff _ hRT m (m + 1) rfl).2
        ((hz (m + 1) (by lia)).eq_of_tgt _ _)
    exact isIso_of_mono_of_epi _
  -- `τ^{≥ -n} L ≅ τ^{≥ -n} K`
  let h := t.descTruncGE g (-(n : ℤ))
  have hπh : T.mor₂ ≫ h = g := t.π_descTruncGE g _
  have hh : IsIso h := by
    rw [DerivedCategory.isIso_iff]
    intro q
    rcases lt_or_ge q (-(n : ℤ)) with hq | hq
    · have h0 : IsZero ((DerivedCategory.homologyFunctor C q).obj T.obj₃) :=
        DerivedCategory.isZero_of_isGE _ (-(n : ℤ)) q hq
      have h0' : IsZero ((DerivedCategory.homologyFunctor C q).obj
          ((DerivedCategory.truncGEOpSequence K).obj (op n))) :=
        DerivedCategory.isZero_of_isGE _ (-(n : ℤ)) q hq
      exact ⟨0, h0.eq_of_src _ _, h0'.eq_of_src _ _⟩
    · have : IsIso ((DerivedCategory.homologyFunctor C q).map T.mor₂) :=
        DerivedCategory.isIso_homologyFunctor_map_truncGEπ_app L _ _ hq
      have : IsIso ((DerivedCategory.homologyFunctor C q).map
          ((t.truncGEπ (-((n + 1 : ℕ) : ℤ))).app K)) :=
        DerivedCategory.isIso_homologyFunctor_map_truncGEπ_app K _ _ (by lia)
      have : IsIso ((DerivedCategory.homologyFunctor C q).map
          ((t.truncGEπ (-(n : ℤ))).app K)) :=
        DerivedCategory.isIso_homologyFunctor_map_truncGEπ_app K _ _ (by lia)
      have hg' : IsIso ((DerivedCategory.homologyFunctor C q).map g) := by
        have e := (DerivedCategory.homologyFunctor C q).congr_map
          (t.π_natTransTruncGEOfLE_app (-((n + 1 : ℕ) : ℤ)) (-(n : ℤ)) (by lia) K)
        rw [Functor.map_comp, ← hg] at e
        have : IsIso ((DerivedCategory.homologyFunctor C q).map
            ((t.truncGEπ (-((n + 1 : ℕ) : ℤ))).app K) ≫
              (DerivedCategory.homologyFunctor C q).map g) := by
          rw [e]
          infer_instance
        exact IsIso.of_isIso_comp_left ((DerivedCategory.homologyFunctor C q).map
          ((t.truncGEπ (-((n + 1 : ℕ) : ℤ))).app K)) _
      have e := (DerivedCategory.homologyFunctor C q).congr_map hπh
      rw [Functor.map_comp] at e
      have : IsIso ((DerivedCategory.homologyFunctor C q).map T.mor₂ ≫
          (DerivedCategory.homologyFunctor C q).map h) := by
        rw [e]
        infer_instance
      exact IsIso.of_isIso_comp_left ((DerivedCategory.homologyFunctor C q).map T.mor₂) _
  have hfinal : IsIso ((DerivedCategory.homologyFunctor D m).map (RF.map g)) := by
    rw [← hπh, RF.map_comp, Functor.map_comp]
    infer_instance
  exact hfinal

end Truncation

section Unbounded

variable {C : Type*} [Category C] [Abelian C] [HasDerivedCategory C] [EnoughInjectives C]
  [Abelian.HasKInjectiveResolutions C] [HasLimitsOfShape (Discrete ℕ) C]
  {R : Type v} [Ring R] [HasDerivedCategory (ModuleCat.{v} R)]
  [Abelian.HasKInjectiveResolutions (ModuleCat.{v} R)]

/-- **Cohomology of unbounded complexes with acyclic cohomology objects** (abstract form of
Stacks, Tag 0BKZ). Let `(Γᵢ)ᵢ` be a family of left exact functors `C ⥤ ModuleCat R` preserving
countable products which *detects* cohomology: an object `N ∈ D(C)` with `Hᵠ(RΓᵢ(N)) = 0` for
all `i` has `Hᵠ(N) = 0` (for sheaves on a site, `Γᵢ` are the sections over a family of
objects covering every object). If `K ∈ D(C)` is such that all `Hᵠ(K)` are `Γᵢ`-acyclic, then
`Hᵠ(RΓᵢ(K)) ≅ Γᵢ(Hᵠ(K))` for all `i` and `q`.

Proof: let `c` be a homotopy limit cone over the tower `τ^{≥ -n} K`. The tower `Hᵐ(RΓᵢ(τ^{≥ -n} K))`
is eventually constant by the acyclicity hypothesis, so the legs of `RΓᵢ(c)` induce isomorphisms
on `Hᵐ` for `n ≫ 0` (Milnor sequence). By detection the legs of `c` induce isomorphisms on `Hᵐ`
for `n ≫ 0`, so the comparison `K ⟶ R lim τ^{≥ -n} K` is an isomorphism, and we conclude by the
bounded below case. -/
theorem nonempty_homology_rightDerivedFunctor_obj_iso_of_acyclic_of_detects {ι : Type*}
    (Γ : ι → C ⥤ ModuleCat.{v} R) [∀ i, (Γ i).Additive] [∀ i, PreservesFiniteLimits (Γ i)]
    [∀ i, PreservesLimitsOfShape (Discrete ℕ) (Γ i)]
    (hΓ : ∀ (N : DerivedCategory C) (q : ℤ), (∀ i, IsZero ((DerivedCategory.homologyFunctor
      (ModuleCat.{v} R) q).obj ((Γ i).rightDerivedFunctor.obj N))) →
        IsZero ((DerivedCategory.homologyFunctor C q).obj N))
    (K : DerivedCategory C)
    (hK : ∀ i q, (Γ i).IsRightAcyclic ((DerivedCategory.homologyFunctor C q).obj K))
    (i : ι) (q : ℤ) :
    Nonempty ((DerivedCategory.homologyFunctor (ModuleCat.{v} R) q).obj
        ((Γ i).rightDerivedFunctor.obj K) ≅
          (Γ i).obj ((DerivedCategory.homologyFunctor C q).obj K)) := by
  let t := DerivedCategory.TStructure.t (C := C)
  let T := DerivedCategory.truncGEOpSequence K
  obtain ⟨c, hc⟩ := Pretriangulated.exists_isHomotopyLimit T
  -- the legs of `c` induce isomorphisms on `Hᵐ(RΓⱼ(-))` for `n ≥ 1 - m`
  have hleg (j : ι) (m : ℤ) (n : ℕ) (hn : 1 - m ≤ n) :
      IsIso ((DerivedCategory.homologyFunctor _ m).map
        ((Γ j).rightDerivedFunctor.map (c.π.app (op n)))) := by
    let RΓ := (Γ j).rightDerivedFunctor
    have := preservesLimitsOfShape_discrete_nat_rightDerivedFunctor (Γ j)
    let n₀ := (1 - m).toNat
    have hc' := (hc.map RΓ).whiskerAdd n₀
    have hall (p : ℤ) (hp : m - 1 ≤ p) (a b : ℕ) (hab : a ≤ b) :
        IsIso ((DerivedCategory.homologyFunctor _ p).map
          ((addOpFunctor n₀ ⋙ T ⋙ RΓ).map (homOfLE hab).op)) :=
      (T ⋙ RΓ ⋙ DerivedCategory.homologyFunctor _ p).isIso_map_homOfLE_op_of_isIso_succ n₀
        (fun k hk ↦ (Γ j).isIso_homology_rightDerivedFunctor_map_truncGEOpSequence_map_succ K k
          (hK j _) p (by lia)) (Nat.add_le_add_right hab n₀) (by lia)
    obtain ⟨k, rfl⟩ : ∃ k, n = k + n₀ := ⟨n - n₀, by lia⟩
    exact DerivedCategory.isIso_homologyFunctor_map_π_of_isHomotopyLimit_of_isIso hc' m
      (hall m (by lia)) (hall (m - 1) le_rfl) k
  -- hence, by detection, the legs of `c` induce isomorphisms on `Hᵐ` for `n ≥ 2 - m`
  have hZ (n : ℕ) (m : ℤ) (hm : 2 - n ≤ m) :
      IsIso ((DerivedCategory.homologyFunctor C m).map (c.π.app (op n))) := by
    obtain ⟨Z, g, h, hT⟩ := distinguished_cocone_triangle (c.π.app (op n))
    have hz (p : ℤ) (hp : 1 - n ≤ p) : IsZero ((DerivedCategory.homologyFunctor C p).obj Z) := by
      refine hΓ Z p fun j ↦ ?_
      have hRT := (Γ j).rightDerivedFunctor.map_distinguished _ hT
      have h₁ : Epi ((DerivedCategory.homologyFunctor _ p).map
          ((Γ j).rightDerivedFunctor.map (c.π.app (op n)))) := by
        have := hleg j p n (by lia)
        infer_instance
      have h₂ : Mono ((DerivedCategory.homologyFunctor _ (p + 1)).map
          ((Γ j).rightDerivedFunctor.map (c.π.app (op n)))) := by
        have := hleg j (p + 1) n (by lia)
        infer_instance
      exact (DerivedCategory.HomologySequence.exact₃ _ hRT p (p + 1) rfl).isZero_X₂
        ((DerivedCategory.HomologySequence.epi_homologyMap_mor₁_iff _ hRT p).1 h₁)
        ((DerivedCategory.HomologySequence.mono_homologyMap_mor₁_iff _ hRT p (p + 1) rfl).1 h₂)
    have hmono : Mono ((DerivedCategory.homologyFunctor C m).map (c.π.app (op n))) :=
      (DerivedCategory.HomologySequence.mono_homologyMap_mor₁_iff _ hT (m - 1) m (by lia)).2
        ((hz (m - 1) (by lia)).eq_of_src _ _)
    have hepi : Epi ((DerivedCategory.homologyFunctor C m).map (c.π.app (op n))) :=
      (DerivedCategory.HomologySequence.epi_homologyMap_mor₁_iff _ hT m).2
        ((hz m (by lia)).eq_of_tgt _ _)
    exact isIso_of_mono_of_epi _
  -- the comparison map `α : K ⟶ c.pt`
  let cK := DerivedCategory.truncGEOpSequenceCone K
  let P := Fan.mk (∏ᶜ fun n : ℕ ↦ T.obj (op n)) (Pi.π fun n : ℕ ↦ T.obj (op n))
  let hP : IsLimit P := productIsProduct _
  obtain ⟨δ, hT⟩ := hc.exists_distTriang hP
  obtain ⟨α, hα⟩ := Triangle.coyoneda_exact₂ _ hT (Fan.IsLimit.lift hP fun n ↦ cK.π.app (op n))
    (Fan.IsLimit.lift_π_comp_one_sub_eq_zero hP (Pretriangulated.towerShift hP)
      (towerShift_proj hP) cK)
  have hαπ (n : ℕ) : α ≫ c.π.app (op n) = cK.π.app (op n) := by
    rw [← Fan.IsLimit.fac hP (fun n ↦ c.π.app (op n)) n,
      ← Fan.IsLimit.fac hP (fun n ↦ cK.π.app (op n)) n, hα, assoc]
    rfl
  have hαiso : IsIso α := by
    rw [DerivedCategory.isIso_iff]
    intro j
    let n := (2 - j).toNat
    have := hZ n j (by lia)
    have : IsIso ((DerivedCategory.homologyFunctor C j).map (α ≫ c.π.app (op n))) := by
      rw [hαπ]
      exact DerivedCategory.isIso_homologyFunctor_map_truncGEπ_app K _ _ (by lia)
    rw [Functor.map_comp] at this
    exact IsIso.of_isIso_comp_right _ ((DerivedCategory.homologyFunctor C j).map (c.π.app (op n)))
  -- conclusion
  let n := (1 - q).toNat
  have hacn (p : ℤ) : (Γ i).IsRightAcyclic
      ((DerivedCategory.homologyFunctor C p).obj (T.obj (op n))) := by
    rcases lt_or_ge p (-(n : ℤ)) with hp | hp
    · exact IsRightAcyclic.of_isZero (DerivedCategory.isZero_of_isGE _ (-(n : ℤ)) p hp)
    · have : IsIso ((DerivedCategory.homologyFunctor C p).map (cK.π.app (op n))) :=
        DerivedCategory.isIso_homologyFunctor_map_truncGEπ_app K _ _ hp
      exact (hK i p).of_iso (asIso ((DerivedCategory.homologyFunctor C p).map
        (cK.π.app (op n)))).symm
  obtain ⟨e⟩ := (Γ i).nonempty_homology_rightDerivedFunctor_obj_iso_of_acyclic (T.obj (op n))
    (-(n : ℤ)) hacn q
  have := hleg i q n (by lia)
  have : IsIso ((DerivedCategory.homologyFunctor C q).map (cK.π.app (op n))) :=
    DerivedCategory.isIso_homologyFunctor_map_truncGEπ_app K _ _ (by lia)
  exact ⟨(DerivedCategory.homologyFunctor _ q).mapIso ((Γ i).rightDerivedFunctor.mapIso
    (asIso α)) ≪≫ asIso ((DerivedCategory.homologyFunctor _ q).map
      ((Γ i).rightDerivedFunctor.map (c.π.app (op n)))) ≪≫ e ≪≫
    (Γ i).mapIso (asIso ((DerivedCategory.homologyFunctor C q).map (cK.π.app (op n)))).symm⟩

end Unbounded

end CategoryTheory.Functor

namespace AlgebraicGeometry.Etale

variable (Λ : Type (u + 1)) [CommRing Λ]

instance additive_sheafSections_obj_moduleCat {X : Scheme.{u}} (U : X.Etaleᵒᵖ) :
    ((sheafSections X.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj U).Additive where
  map_add := rfl

instance preservesLimitsOfShape_sheafSections_obj_moduleCat {X : Scheme.{u}} (U : X.Etaleᵒᵖ)
    (J : Type*) [Category J] [HasLimitsOfShape J (ModuleCat.{u + 1} Λ)] :
    PreservesLimitsOfShape J ((sheafSections X.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj U) :=
  inferInstanceAs (PreservesLimitsOfShape J (sheafToPresheaf X.smallEtaleTopology
    (ModuleCat.{u + 1} Λ) ⋙ (evaluation _ _).obj U))

instance preservesFiniteLimits_sheafSections_obj_moduleCat {X : Scheme.{u}} (U : X.Etaleᵒᵖ) :
    PreservesFiniteLimits ((sheafSections X.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj U) :=
  inferInstanceAs (PreservesFiniteLimits (sheafToPresheaf X.smallEtaleTopology
    (ModuleCat.{u + 1} Λ) ⋙ (evaluation _ _).obj U))

/-- Let `B` be a class of objects of `X_ét` such that every object has a covering by members of
`B`. An object `N ∈ D(X_ét, Λ)` such that `Hᵠ(U, N) = 0` for all `U ∈ B` has `ℋᵠ(N) = 0`:
representing `N` by a K-injective complex `I`, every local section of `ℋᵠ(I)` lifts locally to
a cycle of `I`, which on members of `B` is a boundary. -/
theorem isZero_homology_of_forall_isZero_homology_rightDerivedFunctor_sheafSections
    {X : Scheme.{u}} (B : Set X.Etale)
    (hB : ∀ V : X.Etale,
      Sieve.generate (fun (W : X.Etale) (_ : W ⟶ V) ↦ W ∈ B) ∈ X.smallEtaleTopology V)
    (N : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))) (q : ℤ)
    (hN : ∀ U ∈ B, IsZero ((_root_.DerivedCategory.homologyFunctor (ModuleCat.{u + 1} Λ) q).obj
      (((sheafSections X.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj
        (op U)).rightDerivedFunctor.obj N))) :
    IsZero ((_root_.DerivedCategory.homologyFunctor _ q).obj N) := by
  obtain ⟨I, hI, ⟨e⟩⟩ := _root_.DerivedCategory.exists_iso_Q_obj_of_isKInjective N
  -- `I` is exact in degree `q` on sections over members of `B`
  have hex (U : X.Etale) (hU : U ∈ B) (z : (I.X q).obj.obj (op U))
      (hz : (I.d q (q + 1)).hom.app (op U) z = 0) :
      ∃ y : (I.X (q - 1)).obj.obj (op U), (I.d (q - 1) q).hom.app (op U) y = z := by
    let Γ := (sheafSections X.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj (op U)
    have h₁ : IsZero (((Γ.mapHomologicalComplex _).obj I).homology q) :=
      (hN U hU).of_iso ((_root_.DerivedCategory.homologyFunctor _ q).mapIso
        (Γ.rightDerivedFunctor.mapIso e) ≪≫ (_root_.DerivedCategory.homologyFunctor _ q).mapIso
          (Γ.rightDerivedFunctorObjQIso I) ≪≫
          (_root_.DerivedCategory.homologyFunctorFactors _ q).app _).symm
    have h₂ := (((Γ.mapHomologicalComplex _).obj I).exactAt_iff_isZero_homology q).2 h₁
    rw [HomologicalComplex.exactAt_iff' _ (q - 1) q (q + 1) (by simp) (by simp)] at h₂
    exact (ShortComplex.moduleCat_exact_iff _).1 h₂ z hz
  let S := I.sc' (q - 1) q (q + 1)
  have hepi : Epi S.toCycles := by
    rw [← Sheaf.isLocallySurjective_iff_epi']
    constructor
    intro V s
    refine GrothendieckTopology.superset_covering _ (fun W f hf ↦ ?_) (hB V)
    obtain ⟨W, g, f, hW, rfl⟩ := hf
    refine Sieve.downward_closed _ ?_ g
    have hmono : Mono (S.iCycles.hom.app (op W)) := by
      have : Mono S.iCycles.hom := (sheafToPresheaf _ _).map_mono S.iCycles
      infer_instance
    have hcyc (x : S.cycles.obj.obj (op W)) :
        (I.d q (q + 1)).hom.app (op W) (S.iCycles.hom.app (op W) x) = 0 :=
      (ConcreteCategory.congr_hom (congrArg (fun φ ↦ φ.hom.app (op W)) S.iCycles_g) x).trans
        (by simp)
    have htc (y : (I.X (q - 1)).obj.obj (op W)) :
        S.iCycles.hom.app (op W) (S.toCycles.hom.app (op W) y) =
          (I.d (q - 1) q).hom.app (op W) y :=
      ConcreteCategory.congr_hom (congrArg (fun φ ↦ φ.hom.app (op W)) S.toCycles_i) y
    obtain ⟨y, hy⟩ := hex W hW _ (hcyc (S.cycles.obj.map f.op s))
    exact ⟨y, (ModuleCat.mono_iff_injective _).1 hmono ((htc y).trans hy)⟩
  have hexact : S.Exact := S.exact_iff_epi_toCycles.2 hepi
  have hI' : I.ExactAt q := (I.exactAt_iff' (q - 1) q (q + 1) (by simp) (by simp)).2 hexact
  exact ((I.exactAt_iff_isZero_homology q).1 hI').of_iso
    ((_root_.DerivedCategory.homologyFunctor _ q).mapIso e ≪≫
      (_root_.DerivedCategory.homologyFunctorFactors _ q).app I)

/-- Blueprint `lem-kun-0bkz`: **cohomology of unbounded complexes** (Stacks, Tag 0BKZ). Let `X`
be a scheme, `K ∈ D(X_ét, Λ)` (unbounded), and `B` a class of objects of `X_ét` such that
(1) every object of `X_ét` has a covering by members of `B` and (2) `Hᵖ(U, ℋᵠ(K)) = 0` for all
`p > 0`, all `q` and all `U ∈ B`. Then `Hᵠ(U, K) ≅ H⁰(U, ℋᵠ(K)) = Γ(U, ℋᵠ(K))` for all `q` and
all `U ∈ B`. Here `H^•(U, -)` is the cohomology of the right derived functor of the sections
functor `Γ(U, -)` on `D(X_ét, Λ)`.

The blueprint argues with the hypercohomology spectral sequence; the proof here follows Stacks:
`K` is the derived limit of its truncations `τ^{≥ -n} K`, and `RΓ(U, -)` commutes with derived
limits
(`CategoryTheory.Functor.nonempty_homology_rightDerivedFunctor_obj_iso_of_acyclic_of_detects`,
with the detection property
`Etale.isZero_homology_of_forall_isZero_homology_rightDerivedFunctor_sheafSections`
provided by the coverings by members of `B`). -/
theorem nonempty_homology_rightDerivedFunctor_sheafSections_obj_iso_of_acyclic {X : Scheme.{u}}
    (K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (B : Set X.Etale)
    (hB : ∀ V : X.Etale,
      Sieve.generate (fun (W : X.Etale) (_ : W ⟶ V) ↦ W ∈ B) ∈ X.smallEtaleTopology V)
    (hK : ∀ U ∈ B, ∀ q p : ℤ, 0 < p → IsZero ((_root_.DerivedCategory.homologyFunctor _ p).obj
      (((sheafSections X.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj
        (op U)).rightDerivedFunctor.obj ((_root_.DerivedCategory.singleFunctor _ 0).obj
          ((_root_.DerivedCategory.homologyFunctor _ q).obj K)))))
    {U : X.Etale} (hU : U ∈ B) (q : ℤ) :
    Nonempty ((_root_.DerivedCategory.homologyFunctor (ModuleCat.{u + 1} Λ) q).obj
        (((sheafSections X.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj
          (op U)).rightDerivedFunctor.obj K) ≅
      ((sheafSections X.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj (op U)).obj
        ((_root_.DerivedCategory.homologyFunctor _ q).obj K)) :=
  Functor.nonempty_homology_rightDerivedFunctor_obj_iso_of_acyclic_of_detects
    (fun V : B ↦ (sheafSections X.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj (op V.1))
    (fun N p hN ↦ isZero_homology_of_forall_isZero_homology_rightDerivedFunctor_sheafSections Λ
      B hB N p fun V hV ↦ hN ⟨V, hV⟩) K (fun V q p hp ↦ hK V.1 V.2 q p hp) ⟨U, hU⟩ q


set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- The sections over an étale `X`-scheme `V` are the global sections of the restriction to
`V_ét`: `Γ(V, -) ≅ Γ(V_ét, (V ⟶ X)^* -)`. -/
noncomputable def sheafSectionsIsoUpperStarCompΓ {X : Scheme.{u}} (V : X.Etale) :
    (sheafSections X.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj (op V) ≅
      upperStar (ModuleCat.{u + 1} Λ) V.hom ⋙
        Sheaf.Γ V.left.smallEtaleTopology (ModuleCat.{u + 1} Λ) := by
  let A := ModuleCat.{u + 1} Λ
  let w : V.left.Etale := Scheme.Etale.mk (𝟙 V.left)
  let eW : (MorphismProperty.Over.map ⊤ (inferInstance : Etale V.hom)).obj w ≅ V :=
    MorphismProperty.Over.isoMk (Iso.refl V.left) (by simp [w])
  exact (sheafSections X.smallEtaleTopology A).mapIso eW.op ≪≫
    Functor.isoWhiskerRight (upperStarIsoLocalizationRestriction A V.hom inferInstance).symm
      ((sheafSections V.left.smallEtaleTopology A).obj (op w)) ≪≫
    Functor.isoWhiskerLeft (upperStar A V.hom)
      (Sheaf.ΓNatIsoSheafSections V.left.smallEtaleTopology A
        (MorphismProperty.Over.mkIdTerminal (P := @Etale) V.left)).symm

/-- The cohomology `Hᵖ(V, F)` of a sheaf `F` on `X_ét` over an étale `X`-scheme `V` is the
cohomology `Hᵖ(V_ét, F|_V)` of its restriction: the restriction `(V ⟶ X)^*` is exact and has an
exact left adjoint (extension by zero), so it preserves K-injective complexes. -/
noncomputable def homologyRightDerivedFunctorSheafSectionsSingleIso {X : Scheme.{u}}
    (V : X.Etale) (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (p : ℤ) :
    (_root_.DerivedCategory.homologyFunctor (ModuleCat.{u + 1} Λ) p).obj
        (((sheafSections X.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj
          (op V)).rightDerivedFunctor.obj ((_root_.DerivedCategory.singleFunctor _ 0).obj F)) ≅
      (_root_.DerivedCategory.homologyFunctor (ModuleCat.{u + 1} Λ) p).obj
        ((rightDerivedGlobalSections (ModuleCat.{u + 1} Λ) V.left).obj
          ((_root_.DerivedCategory.singleFunctor _ 0).obj
            ((upperStar (ModuleCat.{u + 1} Λ) V.hom).obj F))) :=
  let T := upperStar (ModuleCat.{u + 1} Λ) V.hom
  let G := Sheaf.Γ V.left.smallEtaleTopology (ModuleCat.{u + 1} Λ)
  have : T.PreservesKInjectiveComplexes :=
    (etaleLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} Λ) V.hom
      inferInstance).preservesKInjectiveComplexes
  (_root_.DerivedCategory.homologyFunctor _ p).mapIso
    ((Functor.rightDerivedFunctorCompIso' T G
      (sheafSectionsIsoUpperStarCompΓ Λ V).symm).symm.app _ ≪≫
      G.rightDerivedFunctor.mapIso (T.singleFunctorCompRightDerivedFunctorIso.app F))


/-- Two geometric points over the same point of a scheme have simultaneously zero stalks for
every étale sheaf of `Λ`-modules (`lem-kun-support-geometric-point-independent`, transported
from abelian groups along the forgetful functor). -/
lemma isZero_sheafFiber_iff_of_same_image_moduleCat {X : Scheme.{u}}
    {Ω Ω' : Type u} [Field Ω] [IsAlgClosed Ω] [Field Ω'] [IsAlgClosed Ω']
    (s : Spec (.of Ω) ⟶ X) (s' : Spec (.of Ω') ⟶ X) (h : s default = s' default)
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    IsZero ((Scheme.pointSmallEtale s).sheafFiber.obj F) ↔
      IsZero ((Scheme.pointSmallEtale s').sheafFiber.obj F) := by
  have : PreservesFilteredColimitsOfSize.{u, u}
      (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}) :=
    preservesFilteredColimitsOfSize_shrink.{u, u + 1, u, u + 1} _
  have key {Ω₀ : Type u} [Field Ω₀] [IsAlgClosed Ω₀] (t : Spec (.of Ω₀) ⟶ X) :
      IsZero ((Scheme.pointSmallEtale t).sheafFiber.obj F) ↔
        IsZero ((Scheme.pointSmallEtale t).sheafFiber.obj ((sheafCompose X.smallEtaleTopology
          (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).obj F)) :=
    (ModuleCat.isZero_iff_subsingleton.trans
      (AddCommGrpCat.isZero_iff_subsingleton : IsZero ((forget₂ (ModuleCat.{u + 1} Λ)
        AddCommGrpCat.{u + 1}).obj ((Scheme.pointSmallEtale t).sheafFiber.obj F)) ↔ _).symm).trans
      (((Scheme.pointSmallEtale t).sheafFiberCompIso
        (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).app F).isZero_iff.symm
  rw [key s, key s']
  exact Scheme.isZero_sheafFiber_iff_of_same_image s s' h _

/-- Under an étale morphism `g : U ⟶ X` with `X` locally of finite type over a field, the
points lying over a closed point are closed: the residue field extensions of `g` are separable,
hence algebraic, and closed points are those with residue field algebraic over the base. -/
lemma isClosed_singleton_of_etale {k : Type u} [Field k] {U X : Scheme.{u}} (g : U ⟶ X)
    [Etale g] (p : X ⟶ Spec (.of k)) [LocallyOfFiniteType p] (u : U) (hx : IsClosed {g u}) :
    IsClosed ({u} : Set U) := by
  let := (p.residueFieldAlgebraMap (g u)).toAlgebra
  have h₁ : Algebra.IsAlgebraic k (X.residueField (g u)) :=
    (p.isClosed_singleton_iff_isAlgebraic_residueField _).1 hx
  let : Algebra (X.residueField (g u)) (U.residueField u) := (g.residueFieldMap u).hom.toAlgebra
  have h₂ : Algebra.IsSeparable (X.residueField (g u)) (U.residueField u) := inferInstance
  let := ((g ≫ p).residueFieldAlgebraMap u).toAlgebra
  have : IsScalarTower k (X.residueField (g u)) (U.residueField u) := by
    refine IsScalarTower.of_algebraMap_eq' ?_
    simp only [RingHom.algebraMap_toAlgebra, Scheme.Hom.residueFieldAlgebraMap,
      Scheme.residueFieldMap_comp, CommRingCat.hom_comp]
    rfl
  rw [(g ≫ p).isClosed_singleton_iff_isAlgebraic_residueField]
  exact Algebra.IsAlgebraic.trans k (X.residueField (g u)) _


/-- Blueprint `lemma-sheaves-finite-support-finite-morphisms--1` on a quasi-compact étale `X`-scheme
`V`: if `X` is locally of finite type over a separably closed field and the stalks of `F` vanish at
the non-closed points of `X`, then `Hᵠ(V, F) = 0` for `q ≠ 0`. Indeed `Hᵠ(V, F) = Hᵠ(V_ét, F|_V)`,
`V` is of finite type over the field, and the points of `V` over closed points of `X` are closed. -/
lemma isZero_homology_rightDerivedFunctor_sheafSections_of_isZero_sheafFiber {K : Type u}
    [Field K] [IsSepClosed K] {X : Scheme.{u}} (p : X ⟶ Spec (.of K)) [LocallyOfFiniteType p]
    (V : X.Etale) [CompactSpace V.left] (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (hF : ∀ x ∉ closedPoints X,
      IsZero ((Scheme.pointSmallEtale (X.algClosurePoint x)).sheafFiber.obj F))
    {q : ℤ} (hq : q ≠ 0) :
    IsZero ((_root_.DerivedCategory.homologyFunctor (ModuleCat.{u + 1} Λ) q).obj
      (((sheafSections X.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj
        (op V)).rightDerivedFunctor.obj ((_root_.DerivedCategory.singleFunctor _ 0).obj F))) := by
  have : CompactSpace ((𝟭 Scheme).obj V.left) := ‹CompactSpace V.left›
  refine (isZero_homology_rightDerivedGlobalSections_of_isZero_sheafFiber Λ (V.hom ≫ p)
    ((upperStar _ V.hom).obj F) (fun u hu ↦ ?_) hq).of_iso
      (homologyRightDerivedFunctorSheafSectionsSingleIso Λ V F q)
  have hx : V.hom u ∉ closedPoints X := fun hx ↦
    hu (isClosed_singleton_of_etale V.hom p u hx)
  refine (Iso.isZero_iff ((upperStarCompSheafFiberIso _ V.hom
    (V.left.algClosurePoint u)).app F)).2 ?_
  refine (isZero_sheafFiber_iff_of_same_image_moduleCat Λ _ (X.algClosurePoint (V.hom u)) ?_
    F).2 (hF _ hx)
  simp

/-- Blueprint `corollary-open-direct-image-over-field--2`: **detection of objects supported at
closed points** (unbounded case). Let `K` be a separably closed field, `X` a scheme of finite type
over `K` (structure morphism `p`, locally of finite type, `X` quasi-compact), and `Q ∈ D(X_ét, Λ)`
(unbounded) such that the stalks of all cohomology sheaves `ℋᵠ(Q)` at the geometric points over
non-closed points of `X` vanish. Then `Q = 0` if and only if `Hⁱ(X_ét, Q) = 0` for all `i`.

Following the blueprint, the class `B` of quasi-compact étale `X`-schemes covers `X_ét`, and
the cohomology sheaves of `Q` are acyclic on its members
(`lemma-sheaves-finite-support-finite-morphisms--1`), so that `Hⁱ(X_ét, Q) = Γ(X, ℋⁱ(Q))` by
`lem-kun-0bkz`; the sheaves `ℋⁱ(Q)` are globally generated
(`corollary-open-direct-image-over-field--2`), hence vanish if they have no global sections. -/
theorem isZero_iff_forall_isZero_homology_rightDerivedGlobalSections {K : Type u} [Field K]
    [IsSepClosed K] {X : Scheme.{u}} (p : X ⟶ Spec (.of K)) [LocallyOfFiniteType p]
    [CompactSpace X]
    (Q : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (hQ : ∀ q : ℤ, ∀ x ∉ closedPoints X,
      IsZero ((Scheme.pointSmallEtale (X.algClosurePoint x)).sheafFiber.obj
        ((_root_.DerivedCategory.homologyFunctor _ q).obj Q))) :
    IsZero Q ↔ ∀ i : ℤ,
      IsZero ((_root_.DerivedCategory.homologyFunctor (ModuleCat.{u + 1} Λ) i).obj
        ((rightDerivedGlobalSections (ModuleCat.{u + 1} Λ) X).obj Q)) := by
  refine ⟨fun h i ↦ (_root_.DerivedCategory.homologyFunctor _ i).map_isZero
    ((rightDerivedGlobalSections _ X).map_isZero h), fun h ↦ ?_⟩
  let B : Set X.Etale := {V | CompactSpace V.left}
  have hB (V : X.Etale) :
      Sieve.generate (fun (W : X.Etale) (_ : W ⟶ V) ↦ W ∈ B) ∈ X.smallEtaleTopology V :=
    mem_smallEtaleTopology_of_forall_isAffine _ fun W g hW ↦
      ⟨W, 𝟙 W, g, (inferInstance : CompactSpace W.left), Category.id_comp g⟩
  have hK (U : X.Etale) (hU : U ∈ B) (q p' : ℤ) (hp : 0 < p') :
      IsZero ((_root_.DerivedCategory.homologyFunctor _ p').obj
        (((sheafSections X.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj
          (op U)).rightDerivedFunctor.obj ((_root_.DerivedCategory.singleFunctor _ 0).obj
            ((_root_.DerivedCategory.homologyFunctor _ q).obj Q)))) := by
    have : CompactSpace U.left := hU
    exact isZero_homology_rightDerivedFunctor_sheafSections_of_isZero_sheafFiber Λ p U _
      (hQ q) hp.ne'
  have hT : etaleTerminal X ∈ B := (inferInstance : CompactSpace X)
  let e := Sheaf.ΓNatIsoSheafSections X.smallEtaleTopology (ModuleCat.{u + 1} Λ)
    (isTerminalEtaleTerminal X)
  refine (_root_.DerivedCategory.isZero_iff Q).2 fun q ↦ ?_
  obtain ⟨φ⟩ := nonempty_homology_rightDerivedFunctor_sheafSections_obj_iso_of_acyclic Λ Q B hB
    hK hT q
  have hΓ := (h q).of_iso ((_root_.DerivedCategory.homologyFunctor _ q).mapIso
    ((Functor.rightDerivedFunctorNatIso e).app Q) ≪≫ φ).symm
  exact isZero_of_isZero_sheafFiber_of_subsingleton _ p (hQ q)
    (ModuleCat.isZero_iff_subsingleton.1 hΓ)

end AlgebraicGeometry.Etale
