/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.StrictHenselizationProductParameters
public import WeilConjectures.AlgebraicGeometry.StrictHenselizationClosedFiberBackward
public import WeilConjectures.TraceFormula.CurveLocal.RestrictionZeroCoverConstruction
public import WeilConjectures.TraceFormula.CurveLocal.ModelVanishing
public import WeilConjectures.AlgebraicGeometry.Curve.SerreDuality

/-!

# The tangent cones of the curves of a cover datum

For a cover datum `p : C ⟶ X`, `c` (blueprint `lemma-tangent-cones-on-cover` (iii)), the tangent
cones of the curves `D' = G' ∪ V'` and `B'`, and of `D'` and `H'`, in `T' = Spec R'` meet only
at the origin
(`AlgebraicGeometry.Etale.CurveLocalModel.CoverDatum.tangentConesMeetAtOrigin_specIdeal`).

Let `ξ` be a uniformizer at `c` and `ξ₁`, `η₁` its images under the two projections; they generate
the maximal ideal of `R'`
(`AlgebraicGeometry.Scheme.strictHenselization_maximalIdeal_eq_span_stalk_pair`, via an affine
chart and `AlgebraicGeometry.Scheme.strictHenselization_maximalIdeal_eq_map_ker`). For a uniformizer
`u` at `y` with `p^♯ u = w ξ^e`, the images `U₁`, `U₂` of `u ⊗ 1`, `1 ⊗ u` are `w₁ ξ₁^e`, `w₂ η₁^e`,
and the image of `1 ⊗ h^♯ u` lies in `(U₂²)`. A function on `X ×_k X` vanishing on a closed
subscheme gives an element of `R'` in the vanishing ideal of its inverse image
(`AlgebraicGeometry.Scheme.ΓSpecIso_hom_appLE_sub_mem_asIdeal`), so `U₁ (U₁ - Φ)`, `U₁ - U₂` and
`η₁` lie in the ideals of `D'`, `B'` and `H'`, with initial forms `w₁² ξ₁^{2e}`,
`w₁ ξ₁^e - w₂ η₁^e` and `η₁`.

-/

@[expose] public section

universe u

open CategoryTheory Limits IsLocalRing

namespace AlgebraicGeometry.Scheme

section LocalRingHom

variable {R : CommRingCat.{u}} {X Y : Scheme.{u}}

/-- For a morphism `ψ : Spec R ⟶ X` from the spectrum of a local ring and a point `x` of `X`
equal to the image of the closed point, the induced local ring map `𝒪_{X,x} ⟶ R`. -/
noncomputable def stalkClosedPointToOfEq [IsLocalRing R] (ψ : Spec R ⟶ X) (x : X)
    (hx : ψ (closedPoint R) = x) :
    X.presheaf.stalk x ⟶ R :=
  X.presheaf.stalkSpecializes (specializes_of_eq hx) ≫ stalkClosedPointTo ψ

instance isLocalHom_stalkClosedPointToOfEq [IsLocalRing R] (ψ : Spec R ⟶ X) (x : X)
    (hx : ψ (closedPoint R) = x) : IsLocalHom (stalkClosedPointToOfEq ψ x hx).hom := by
  subst hx
  rw [stalkClosedPointToOfEq, TopCat.Presheaf.stalkSpecializes_refl, Category.id_comp]
  infer_instance

lemma stalkClosedPointToOfEq_germ [IsLocalRing R] (ψ : Spec R ⟶ X) (x : X)
    (hx : ψ (closedPoint R) = x) (U : X.Opens) (hxU : x ∈ U) (s : Γ(X, U)) :
    stalkClosedPointToOfEq ψ x hx (X.presheaf.germ U x hxU s) =
      (ΓSpecIso R).hom (ψ.appLE U ⊤ (preimage_eq_top_of_closedPoint_mem ψ (hx ▸ hxU)).ge s) := by
  subst hx
  rw [stalkClosedPointToOfEq, TopCat.Presheaf.stalkSpecializes_refl, Category.id_comp,
    ← CommRingCat.comp_apply, germ_stalkClosedPointTo]
  simp only [Hom.appLE, Iso.trans_hom, Functor.mapIso_hom, Iso.op_hom, eqToIso.hom,
    CommRingCat.comp_apply]
  rfl

lemma isLocalHom_stalkSpecializes_of_eq (x y : X) (h : x = y) :
    IsLocalHom (X.presheaf.stalkSpecializes (specializes_of_eq h)).hom := by
  subst h
  rw [TopCat.Presheaf.stalkSpecializes_refl]
  infer_instance

lemma stalkClosedPointToOfEq_comp [IsLocalRing R] (ψ : Spec R ⟶ X) (φ : X ⟶ Y) (x : X)
    (hx : ψ (closedPoint R) = x) (y : Y) (hy : φ x = y) :
    stalkClosedPointToOfEq (ψ ≫ φ) y (by rw [Hom.comp_apply, hx, hy]) =
      Y.presheaf.stalkSpecializes (specializes_of_eq hy) ≫ φ.stalkMap x ≫
        stalkClosedPointToOfEq ψ x hx := by
  subst hx hy
  simp only [stalkClosedPointToOfEq, TopCat.Presheaf.stalkSpecializes_refl, Category.id_comp]
  exact stalkClosedPointTo_comp ψ φ

lemma stalkClosedPointToOfEq_congr [IsLocalRing R] {ψ ψ' : Spec R ⟶ X} (h : ψ = ψ') (x : X)
    (hx : ψ (closedPoint R) = x) :
    stalkClosedPointToOfEq ψ x hx = stalkClosedPointToOfEq ψ' x (h ▸ hx) := by
  subst h
  rfl

/-- The image in `R` of a function `s` on `X` lies in the prime `z` iff `s` vanishes at `ψ z`. -/
lemma ΓSpecIso_hom_appLE_mem_asIdeal_iff (ψ : Spec R ⟶ X) {U : X.Opens} (e : ⊤ ≤ ψ ⁻¹ᵁ U)
    (s : Γ(X, U)) (z : Spec R) :
    (ΓSpecIso R).hom (ψ.appLE U ⊤ e s) ∈ z.asIdeal ↔ ψ z ∉ X.basicOpen s := by
  have h := congrArg (z ∈ ·) (basicOpen_appLE ψ ⊤ U e s)
  simp only [basicOpen_eq_of_affine'] at h
  rw [← not_iff_not, not_not, ← PrimeSpectrum.mem_basicOpen, eq_iff_iff.mp h,
    TopologicalSpace.Opens.mem_inf]
  exact ⟨fun h ↦ h.2, fun h ↦ ⟨trivial, h⟩⟩

/-- If `ι ≫ φ₁ = ι ≫ φ₂`, the difference of the pullbacks of a function `s` along `φ₁` and `φ₂`
vanishes on the image of `ι`. -/
lemma notMem_basicOpen_appLE_sub_appLE {Z : Scheme.{u}} (φ₁ φ₂ : Y ⟶ X) {U : X.Opens}
    (s : Γ(X, U)) (ι : Z ⟶ Y) (hι : ι ≫ φ₁ = ι ≫ φ₂) (t : Z)
    (ht : ι t ∈ φ₁ ⁻¹ᵁ U ⊓ φ₂ ⁻¹ᵁ U) :
    ι t ∉ Y.basicOpen (φ₁.appLE U (φ₁ ⁻¹ᵁ U ⊓ φ₂ ⁻¹ᵁ U) inf_le_left s -
      φ₂.appLE U (φ₁ ⁻¹ᵁ U ⊓ φ₂ ⁻¹ᵁ U) inf_le_right s) := by
  intro hmem
  have h := basicOpen_appLE ι (ι ⁻¹ᵁ (φ₁ ⁻¹ᵁ U ⊓ φ₂ ⁻¹ᵁ U)) _ le_rfl
    (φ₁.appLE U (φ₁ ⁻¹ᵁ U ⊓ φ₂ ⁻¹ᵁ U) inf_le_left s -
      φ₂.appLE U (φ₁ ⁻¹ᵁ U ⊓ φ₂ ⁻¹ᵁ U) inf_le_right s)
  rw [map_sub, ← CommRingCat.comp_apply, ← CommRingCat.comp_apply, Hom.appLE_comp_appLE,
    Hom.appLE_comp_appLE, Hom.appLE_congr_hom hι _ _ _
      fun x (hx : ι x ∈ φ₁ ⁻¹ᵁ U ⊓ φ₂ ⁻¹ᵁ U) ↦ hx.2, sub_self,
    basicOpen_zero] at h
  have : t ∈ (⊥ : Z.Opens) := by
    rw [h]
    exact ⟨ht, hmem⟩
  exact this

/-- Variant of `notMem_basicOpen_appLE_sub_appLE` for the images in a local ring `R` of the
pullbacks along `ψ ≫ φ₁` and `ψ ≫ φ₂`, at a prime `z` with `ψ z` in the image of `ι`. -/
lemma ΓSpecIso_hom_appLE_sub_mem_asIdeal {Z : Scheme.{u}} (ψ : Spec R ⟶ Y) (φ₁ φ₂ : Y ⟶ X)
    {U : X.Opens} (s : Γ(X, U)) (e₁ : ⊤ ≤ (ψ ≫ φ₁) ⁻¹ᵁ U) (e₂ : ⊤ ≤ (ψ ≫ φ₂) ⁻¹ᵁ U)
    (ι : Z ⟶ Y) (hι : ι ≫ φ₁ = ι ≫ φ₂) (z : Spec R) (hz : ψ z ∈ Set.range ι) :
    (ΓSpecIso R).hom ((ψ ≫ φ₁).appLE U ⊤ e₁ s) - (ΓSpecIso R).hom ((ψ ≫ φ₂).appLE U ⊤ e₂ s) ∈
      z.asIdeal := by
  have e : ⊤ ≤ ψ ⁻¹ᵁ (φ₁ ⁻¹ᵁ U ⊓ φ₂ ⁻¹ᵁ U) := le_inf e₁ e₂
  have h := (ΓSpecIso_hom_appLE_mem_asIdeal_iff ψ e
    (φ₁.appLE U (φ₁ ⁻¹ᵁ U ⊓ φ₂ ⁻¹ᵁ U) inf_le_left s -
      φ₂.appLE U (φ₁ ⁻¹ᵁ U ⊓ φ₂ ⁻¹ᵁ U) inf_le_right s) z).mpr
  have hc (φ : Y ⟶ X) (e' : φ₁ ⁻¹ᵁ U ⊓ φ₂ ⁻¹ᵁ U ≤ φ ⁻¹ᵁ U) (e'' : ⊤ ≤ (ψ ≫ φ) ⁻¹ᵁ U) :
      ψ.appLE _ ⊤ e (φ.appLE U _ e' s) = (ψ ≫ φ).appLE U ⊤ e'' s := by
    rw [← CommRingCat.comp_apply, Hom.appLE_comp_appLE]
  rw [map_sub, map_sub, hc φ₁ inf_le_left e₁, hc φ₂ inf_le_right e₂] at h
  obtain ⟨t, ht⟩ := hz
  refine h ?_
  rw [← ht]
  exact notMem_basicOpen_appLE_sub_appLE φ₁ φ₂ s ι hι t (ht ▸ e trivial)

/-- A morphism `ψ : Spec R ⟶ X` into an affine open `V` is recovered from its map on sections
over `V`. -/
lemma Spec_map_appLE_comp_fromSpec (ψ : Spec R ⟶ X) {V : X.Opens} (hV : IsAffineOpen V)
    (e : ⊤ ≤ ψ ⁻¹ᵁ V) :
    Spec.map (ψ.appLE V ⊤ e ≫ (ΓSpecIso R).hom) ≫ hV.fromSpec = ψ := by
  rw [Spec.map_comp, Category.assoc, IsAffineOpen.SpecMap_appLE_fromSpec ψ hV (isAffineOpen_top _),
    IsAffineOpen.fromSpec_top, ← isoSpec_Spec_hom, Iso.hom_inv_id_assoc]


end LocalRingHom

open scoped TensorProduct

/-- Let `C₁`, `C₂` be schemes over an algebraically closed field `k`, with affine open charts
`i₁ : Spec A₁ ⟶ C₁`, `i₂ : Spec A₂ ⟶ C₂` over `k`, and `k`-points `φ₁ : A₁ → k`,
`φ₂ : A₂ → k`, and let `s` be the corresponding `k`-point of `C₁ ×_k C₂`. Then the strict
henselization of `C₁ ×_k C₂` at `s` receives a ring map `ρ` from `A₁ ⊗[k] A₂`, compatible with
the chart, and its maximal ideal is generated by the images of `ker φ₁ ⊗ 1` and `1 ⊗ ker φ₂`. -/
theorem strictHenselization_maximalIdeal_eq_map_ker {k : Type u} [Field k] [IsAlgClosed k]
    {C₁ C₂ : Scheme.{u}} (a₁ : C₁ ⟶ Spec (.of k)) (a₂ : C₂ ⟶ Spec (.of k))
    {A₁ A₂ : Type u} [CommRing A₁] [CommRing A₂] [Algebra k A₁] [Algebra k A₂]
    (i₁ : Spec (.of A₁) ⟶ C₁) (i₂ : Spec (.of A₂) ⟶ C₂) [IsOpenImmersion i₁]
    [IsOpenImmersion i₂]
    (hi₁ : i₁ ≫ a₁ = Spec.map (CommRingCat.ofHom (algebraMap k A₁)))
    (hi₂ : i₂ ≫ a₂ = Spec.map (CommRingCat.ofHom (algebraMap k A₂)))
    (φ₁ : A₁ →ₐ[k] k) (φ₂ : A₂ →ₐ[k] k)
    (s : Spec (.of k) ⟶ pullback a₁ a₂)
    (hs₁ : s ≫ pullback.fst a₁ a₂ = Spec.map (CommRingCat.ofHom φ₁.toRingHom) ≫ i₁)
    (hs₂ : s ≫ pullback.snd a₁ a₂ = Spec.map (CommRingCat.ofHom φ₂.toRingHom) ≫ i₂) :
    ∃ ρ : CommRingCat.of (A₁ ⊗[k] A₂) ⟶ strictHenselization s,
      Spec.map ρ ≫ productChart a₁ a₂ i₁ i₂ hi₁ hi₂ = strictLocalizationToBase s ∧
      IsLocalRing.maximalIdeal (strictHenselization s) =
        ((RingHom.ker φ₁).map (Algebra.TensorProduct.includeLeft : A₁ →ₐ[k] A₁ ⊗[k] A₂) ⊔
          (RingHom.ker φ₂).map (Algebra.TensorProduct.includeRight : A₂ →ₐ[k] A₁ ⊗[k] A₂)).map
            ρ.hom := by
  let φ : A₁ ⊗[k] A₂ →ₐ[k] k :=
    Algebra.TensorProduct.lift φ₁ φ₂ (fun _ _ ↦ Commute.all _ _)
  obtain rfl : s = Spec.map (CommRingCat.ofHom (φ : A₁ ⊗[k] A₂ →+* k)) ≫
      productChart a₁ a₂ i₁ i₂ hi₁ hi₂ := by
    refine pullback.hom_ext ?_ ?_
    · rw [hs₁, productChart, Category.assoc, Category.assoc, pullback.lift_fst,
        pullbackSpecIso_inv_fst_assoc, ← Category.assoc, ← Spec.map_comp]
      congr 3
      ext a
      exact ((Algebra.TensorProduct.lift_tmul φ₁ φ₂ (fun _ _ ↦ Commute.all _ _) a 1).trans
        (by simp)).symm
    · rw [hs₂, productChart, Category.assoc, Category.assoc, pullback.lift_snd,
        pullbackSpecIso_inv_snd_assoc, ← Category.assoc, ← Spec.map_comp]
      congr 3
      ext a
      exact ((Algebra.TensorProduct.lift_tmul φ₁ φ₂ (fun _ _ ↦ Commute.all _ _) 1 a).trans
        (by simp)).symm
  obtain ⟨_, ρ, hρ, hm⟩ := strictHenselization_chart_maximalIdeal (CommRingCat.of (A₁ ⊗[k] A₂))
    (productChart a₁ a₂ i₁ i₂ hi₁ hi₂) (Spec.map (CommRingCat.ofHom (φ : A₁ ⊗[k] A₂ →+* k)))
  refine ⟨ρ, hρ, ?_⟩
  rw [hm, Spec_map_closedPoint_asIdeal, Algebra.TensorProduct.ker_lift_eq φ₁ φ₂]

/-- The image of the closed point of the strict localization at `s` is the point of `s`. -/
lemma strictLocalizationToBase_closedPoint {S : Scheme.{u}} {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (s : Spec (.of Ω) ⟶ S) :
    strictLocalizationToBase s (closedPoint (strictHenselization s)) = s default := by
  have := strictHenselizationStructuralMap_closedPoint_eq (A := strictHenselization s) s
    (Iso.refl _)
  rw [Iso.refl_hom, Category.id_comp] at this
  exact this.trans (congrArg _ (Subsingleton.elim _ _))

/-- An affine chart of a scheme `C` over `k` through a `k`-point `c`: an affine open `V ∋ c`,
the `k`-algebra structure on `Γ(C, V)` and the `k`-point `φ : Γ(C, V) → k` of `c`; the functions
in the kernel of `φ` vanish at `c`. -/
lemma exists_affineChart_of_point {k : Type u} [Field k] {C : Scheme.{u}}
    (a : C ⟶ Spec (.of k)) (c : Spec (.of k) ⟶ C) (hc : c ≫ a = 𝟙 _) :
    ∃ (V : C.Opens) (hV : IsAffineOpen V) (hcV : c default ∈ V) (_ : Algebra k Γ(C, V))
      (_ : hV.fromSpec ≫ a = Spec.map (CommRingCat.ofHom (algebraMap k Γ(C, V))))
      (φ : Γ(C, V) →ₐ[k] k), Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ hV.fromSpec = c ∧
        ∀ x ∈ RingHom.ker φ, C.presheaf.germ V (c default) hcV x ∈ maximalIdeal _ := by
  obtain ⟨_, ⟨V, hV, rfl⟩, hcV, -⟩ := C.isBasis_affineOpens.exists_subset_of_mem_open
    (Set.mem_univ (c default)) isOpen_univ
  have hc' : c (closedPoint k) = c default := congrArg _ (Subsingleton.elim _ _)
  have eV : ⊤ ≤ c ⁻¹ᵁ V := (preimage_eq_top_of_closedPoint_mem c (hc' ▸ hcV)).ge
  let : Algebra k Γ(C, V) :=
    ((ΓSpecIso (.of k)).inv ≫ a.appLE ⊤ V le_top).hom.toAlgebra
  have hcomm : (ΓSpecIso (.of k)).inv ≫ a.appLE ⊤ V le_top ≫ c.appLE V ⊤ eV ≫
      (ΓSpecIso (.of k)).hom = 𝟙 _ := by
    rw [Hom.appLE_comp_appLE_assoc, Hom.appLE_congr_hom hc _ _ _ (by simp)]
    simp [Hom.appLE]
  let φ : Γ(C, V) →ₐ[k] k :=
    { toRingHom := (c.appLE V ⊤ eV ≫ (ΓSpecIso (.of k)).hom).hom
      commutes' r := by
        rw [RingHom.algebraMap_toAlgebra]
        exact congrArg (fun f ↦ f.hom r) hcomm }
  refine ⟨V, hV, hcV, inferInstance, ?_, φ, ?_, fun x hx ↦ ?_⟩
  · rw [RingHom.algebraMap_toAlgebra, CommRingCat.ofHom_hom, Spec.map_comp,
      ← IsAffineOpen.SpecMap_appLE_fromSpec a (isAffineOpen_top _) hV le_top,
      IsAffineOpen.fromSpec_top]
    refine congrArg _ ((Iso.hom_comp_eq_id _).mp ?_).symm
    rw [isoSpec_Spec_hom, ← Spec.map_comp, Iso.inv_hom_id, Spec.map_id]
  · exact Spec_map_appLE_comp_fromSpec c hV eV
  · have h0 : stalkClosedPointToOfEq c (c default) hc' (C.presheaf.germ V (c default) hcV x) =
        0 := by
      rw [stalkClosedPointToOfEq_germ]
      exact hx
    rw [mem_maximalIdeal, mem_nonunits_iff]
    intro hu
    have := hu.map (stalkClosedPointToOfEq c (c default) hc').hom
    rw [h0] at this
    exact not_isUnit_zero this


lemma strictLocalizationToBase_comp_closedPoint {S Y : Scheme.{u}} {Ω : Type u} [Field Ω]
    [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ S) (f : S ⟶ Y) (y : Spec (.of Ω) ⟶ Y) (h : s ≫ f = y) :
    (strictLocalizationToBase s ≫ f) (closedPoint (strictHenselization s)) = y default := by
  rw [Hom.comp_apply, strictLocalizationToBase_closedPoint, ← Hom.comp_apply, h]

lemma map_mem_maximalIdeal_of_isLocalHom {A B : CommRingCat.{u}} [IsLocalRing A] [IsLocalRing B]
    (f : A ⟶ B) [IsLocalHom f.hom] {x : A} (hx : x ∈ maximalIdeal A) : f x ∈ maximalIdeal B :=
  (mem_maximalIdeal _).mpr fun h ↦ (mem_maximalIdeal _).mp hx (isUnit_of_map_unit f.hom x h)

/-- Let `C₁`, `C₂` be schemes over an algebraically closed field `k` with `k`-points `c₁`, `c₂`
whose local rings have principal maximal ideals `(ξ)`, `(η)`, and `s = (c₁, c₂)`. Then the
maximal ideal of the strict henselization of `C₁ ×_k C₂` at `s` is generated by the images of
`ξ` and `η` under the two projections (blueprint `lemma-tangent-cones-on-cover` (ii)). -/
theorem strictHenselization_maximalIdeal_eq_span_stalk_pair {k : Type u} [Field k] [IsAlgClosed k]
    {C₁ C₂ : Scheme.{u}} (a₁ : C₁ ⟶ Spec (.of k)) (a₂ : C₂ ⟶ Spec (.of k))
    (c₁ : Spec (.of k) ⟶ C₁) (c₂ : Spec (.of k) ⟶ C₂) (hc₁ : c₁ ≫ a₁ = 𝟙 _)
    (hc₂ : c₂ ≫ a₂ = 𝟙 _) (s : Spec (.of k) ⟶ pullback a₁ a₂)
    (hs₁ : s ≫ pullback.fst a₁ a₂ = c₁) (hs₂ : s ≫ pullback.snd a₁ a₂ = c₂)
    {ξ : C₁.presheaf.stalk (c₁ default)} {η : C₂.presheaf.stalk (c₂ default)}
    (hξ : Ideal.span {ξ} = maximalIdeal _) (hη : Ideal.span {η} = maximalIdeal _) :
    maximalIdeal (strictHenselization s) = Ideal.span
      {stalkClosedPointToOfEq (strictLocalizationToBase s ≫ pullback.fst a₁ a₂) (c₁ default)
          (strictLocalizationToBase_comp_closedPoint s _ c₁ hs₁) ξ,
        stalkClosedPointToOfEq (strictLocalizationToBase s ≫ pullback.snd a₁ a₂) (c₂ default)
          (strictLocalizationToBase_comp_closedPoint s _ c₂ hs₂) η} := by
  obtain ⟨V₁, hV₁, hcV₁, _, hi₁, φ₁, hφ₁, hker₁⟩ := exists_affineChart_of_point a₁ c₁ hc₁
  obtain ⟨V₂, hV₂, hcV₂, _, hi₂, φ₂, hφ₂, hker₂⟩ := exists_affineChart_of_point a₂ c₂ hc₂
  obtain ⟨ρ, hρ, hm⟩ := strictHenselization_maximalIdeal_eq_map_ker a₁ a₂ hV₁.fromSpec
    hV₂.fromSpec hi₁ hi₂ φ₁ φ₂ s (by rw [hs₁, hφ₁]) (by rw [hs₂, hφ₂])
  have hρ₁ (x : Γ(C₁, V₁)) : ρ (x ⊗ₜ 1) = stalkClosedPointToOfEq
      (strictLocalizationToBase s ≫ pullback.fst a₁ a₂) (c₁ default)
      (strictLocalizationToBase_comp_closedPoint s _ c₁ hs₁) (C₁.presheaf.germ V₁ _ hcV₁ x) := by
    rw [stalkClosedPointToOfEq_germ]
    have : CommRingCat.ofHom Algebra.TensorProduct.includeLeftRingHom ≫ ρ =
        (strictLocalizationToBase s ≫ pullback.fst a₁ a₂).appLE V₁ ⊤
          (preimage_eq_top_of_closedPoint_mem _
            ((strictLocalizationToBase_comp_closedPoint s _ c₁ hs₁).symm ▸ hcV₁)).ge ≫
          (ΓSpecIso _).hom := by
      refine Spec.map_injective ((cancel_mono hV₁.fromSpec).mp ?_)
      rw [Spec_map_appLE_comp_fromSpec, ← hρ, Spec.map_comp, Category.assoc, Category.assoc,
        productChart, Category.assoc, pullback.lift_fst, pullbackSpecIso_inv_fst_assoc]
    exact congrArg (fun f ↦ f.hom x) this
  have hρ₂ (x : Γ(C₂, V₂)) : ρ (1 ⊗ₜ x) = stalkClosedPointToOfEq
      (strictLocalizationToBase s ≫ pullback.snd a₁ a₂) (c₂ default)
      (strictLocalizationToBase_comp_closedPoint s _ c₂ hs₂) (C₂.presheaf.germ V₂ _ hcV₂ x) := by
    rw [stalkClosedPointToOfEq_germ]
    have : CommRingCat.ofHom Algebra.TensorProduct.includeRight.toRingHom ≫ ρ =
        (strictLocalizationToBase s ≫ pullback.snd a₁ a₂).appLE V₂ ⊤
          (preimage_eq_top_of_closedPoint_mem _
            ((strictLocalizationToBase_comp_closedPoint s _ c₂ hs₂).symm ▸ hcV₂)).ge ≫
          (ΓSpecIso _).hom := by
      refine Spec.map_injective ((cancel_mono hV₂.fromSpec).mp ?_)
      rw [Spec_map_appLE_comp_fromSpec, ← hρ, Spec.map_comp, Category.assoc, Category.assoc,
        productChart, Category.assoc, pullback.lift_snd, pullbackSpecIso_inv_snd_assoc]
      rfl
    exact congrArg (fun f ↦ f.hom x) this
  refine le_antisymm ?_ ?_
  · rw [hm, Ideal.map_le_iff_le_comap]
    refine sup_le ?_ ?_
    · rw [Ideal.map_le_iff_le_comap]
      intro x hx
      obtain ⟨b, hb⟩ := Ideal.mem_span_singleton'.mp (hξ ▸ hker₁ x hx)
      rw [Ideal.mem_comap, Ideal.mem_comap,
        Algebra.TensorProduct.includeLeft_apply, hρ₁, ← hb, map_mul]
      exact Ideal.mul_mem_left _ _ (Ideal.subset_span (by simp))
    · rw [Ideal.map_le_iff_le_comap]
      intro x hx
      obtain ⟨b, hb⟩ := Ideal.mem_span_singleton'.mp (hη ▸ hker₂ x hx)
      rw [Ideal.mem_comap, Ideal.mem_comap,
        Algebra.TensorProduct.includeRight_apply, hρ₂, ← hb, map_mul]
      exact Ideal.mul_mem_left _ _ (Ideal.subset_span (by simp))
  · rw [Ideal.span_le, Set.insert_subset_iff, Set.singleton_subset_iff]
    exact ⟨map_mem_maximalIdeal_of_isLocalHom _ (hξ ▸ Ideal.mem_span_singleton_self ξ),
      map_mem_maximalIdeal_of_isLocalHom _ (hη ▸ Ideal.mem_span_singleton_self η)⟩


end AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.Etale

/-- The ideal of the reduced closed subscheme `Spec (R ⧸ I(Z))` is the vanishing ideal `I(Z)`. -/
lemma specIdeal_reducedClosedι (R : CommRingCat.{u}) (Z : Set (PrimeSpectrum R)) :
    specIdeal (Scheme.reducedClosedι R Z) = PrimeSpectrum.vanishingIdeal Z := by
  rw [specIdeal, ← Scheme.ΓSpecIso_inv_naturality, CommRingCat.hom_comp,
    RingHom.ker_comp_of_injective, CommRingCat.hom_ofHom, Ideal.mk_ker]
  exact (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso _).inv).1

end AlgebraicGeometry.Etale


namespace AlgebraicGeometry.Etale.CurveLocalModel.CoverDatum

open Scheme

variable {k : Type u} [Field k] [IsAlgClosed k] {M : CurveLocalModel k} {ℓ : ℕ}
  {Λ : Type (u + 1)} [CommRing Λ]
  {PL PK : CochainComplex (Sheaf M.X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) ℤ}
  (D : M.CoverDatum ℓ PL PK)



/-- **Tangent cones** (blueprint `lemma-tangent-cones-on-cover` (iii)): in the regular
parameters `ξ₁ = ξ ⊗ 1`, `η₁ = 1 ⊗ ξ` of `T'`, with `u ⊗ 1 ↦ w₁ ξ₁^e` and `1 ⊗ u ↦ w₂ η₁^e`,
the curve `G' ∪ V'` contains `(u ⊗ 1)(u ⊗ 1 - 1 ⊗ h^♯ u)` with initial form `w₁² ξ₁^{2e}`, the
curve `B'` contains `u ⊗ 1 - 1 ⊗ u = w₁ ξ₁^e - w₂ η₁^e` and `H'` contains `η₁`. -/
theorem tangentConesMeetAtOrigin_specIdeal :
    IsLocalRing.TangentConesMeetAtOrigin (strictHenselization D.s') (specIdeal D.dD')
        (specIdeal D.dB') ∧
      IsLocalRing.TangentConesMeetAtOrigin (strictHenselization D.s') (specIdeal D.dD')
        (specIdeal D.dH') := by
  -- a uniformizer `ϖ` at `y`, the germ of a function `ũ` on `Ux`
  obtain ⟨_, _⟩ := isDiscreteValuationRing_stalk_of_isClosed M.f M.isClosed_y
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible
    (M.X.presheaf.stalk (M.y (default : Spec (.of k))))
  obtain ⟨Ux, hyU, ũ, hũ⟩ := TopCat.Presheaf.exists_germ_eq M.X.presheaf ϖ
  obtain ⟨w, ξ, hw, hξ, hram⟩ := D.ramification ϖ hϖ.maximalIdeal_eq.symm
  have hpc : D.p (D.c default) = M.y default := by
    rw [← Hom.comp_apply, D.c_comp]
  have hhy : M.h (M.y default) = M.y default := by
    rw [← Hom.comp_apply, M.y_comp_h]
  have hq₁ := strictLocalizationToBase_comp_closedPoint D.s' _ D.c D.s'_fst
  have hq₂ := strictLocalizationToBase_comp_closedPoint D.s' _ D.c D.s'_snd
  have hψ₁' : (D.π ≫ M.τ) ≫ pullback.fst M.f M.f =
      (strictLocalizationToBase D.s' ≫ pullback.fst D.fC D.fC) ≫ D.p := by
    rw [π_comp_τ, Category.assoc, g_fst, Category.assoc]
  have hψ₂' : (D.π ≫ M.τ) ≫ pullback.snd M.f M.f =
      (strictLocalizationToBase D.s' ≫ pullback.snd D.fC D.fC) ≫ D.p := by
    rw [π_comp_τ, Category.assoc, g_snd, Category.assoc]
  have hψ₁ : ((D.π ≫ M.τ) ≫ pullback.fst M.f M.f) (closedPoint (strictHenselization D.s')) =
      M.y default := by
    rw [hψ₁', Hom.comp_apply, hq₁, hpc]
  have hψ₂ : ((D.π ≫ M.τ) ≫ pullback.snd M.f M.f) (closedPoint _) = M.y default := by
    rw [hψ₂', Hom.comp_apply, hq₂, hpc]
  have hψ₃ : ((D.π ≫ M.τ) ≫ pullback.snd M.f M.f ≫ M.h) (closedPoint _) = M.y default := by
    rw [← Category.assoc, Hom.comp_apply, hψ₂, hhy]
  set j₁ := stalkClosedPointToOfEq (strictLocalizationToBase D.s' ≫ pullback.fst D.fC D.fC)
    (D.c default) hq₁
  set j₂ := stalkClosedPointToOfEq (strictLocalizationToBase D.s' ≫ pullback.snd D.fC D.fC)
    (D.c default) hq₂
  set ξ₁ := j₁ ξ
  set η₁ := j₂ ξ
  have hm : maximalIdeal (strictHenselization D.s') = Ideal.span {ξ₁, η₁} :=
    strictHenselization_maximalIdeal_eq_span_stalk_pair D.fC D.fC D.c D.c D.c_comp_fC
      D.c_comp_fC D.s' D.s'_fst D.s'_snd hξ hξ
  have hξ₁ : ξ₁ ∈ maximalIdeal (strictHenselization D.s') := hm ▸ Ideal.subset_span (by simp)
  have hη₁ : η₁ ∈ maximalIdeal (strictHenselization D.s') := hm ▸ Ideal.subset_span (by simp)
  -- the images `U₁`, `U₂` of `u ⊗ 1`, `1 ⊗ u` and `Φ` of `1 ⊗ h^♯ u`
  set U₁ := (ΓSpecIso _).hom (((D.π ≫ M.τ) ≫ pullback.fst M.f M.f).appLE Ux ⊤
    (preimage_eq_top_of_closedPoint_mem _ (hψ₁ ▸ hyU)).ge ũ) with hU₁d
  set U₂ := (ΓSpecIso _).hom (((D.π ≫ M.τ) ≫ pullback.snd M.f M.f).appLE Ux ⊤
    (preimage_eq_top_of_closedPoint_mem _ (hψ₂ ▸ hyU)).ge ũ) with hU₂d
  set Φ := (ΓSpecIso _).hom (((D.π ≫ M.τ) ≫ pullback.snd M.f M.f ≫ M.h).appLE Ux ⊤
    (preimage_eq_top_of_closedPoint_mem _ (hψ₃ ▸ hyU)).ge ũ) with hΦd
  have hU₁ : U₁ = j₁ w * ξ₁ ^ D.e := by
    rw [hU₁d, ← stalkClosedPointToOfEq_germ _ _ hψ₁ _ hyU, hũ, stalkClosedPointToOfEq_congr hψ₁',
      stalkClosedPointToOfEq_comp _ _ _ hq₁ _ hpc]
    rw [← Category.assoc, CommRingCat.comp_apply, hram, map_mul, map_pow]
  have hU₂ : U₂ = j₂ w * η₁ ^ D.e := by
    rw [hU₂d, ← stalkClosedPointToOfEq_germ _ _ hψ₂ _ hyU, hũ, stalkClosedPointToOfEq_congr hψ₂',
      stalkClosedPointToOfEq_comp _ _ _ hq₂ _ hpc]
    rw [← Category.assoc, CommRingCat.comp_apply, hram, map_mul, map_pow]
  have hΦ : ∃ b, Φ = U₂ ^ 2 * b := by
    have := isLocalHom_stalkSpecializes_of_eq _ _ hhy
    have ht := map_mem_maximalIdeal_of_isLocalHom
      (M.X.presheaf.stalkSpecializes (specializes_of_eq hhy))
      (hϖ.maximalIdeal_eq ▸ Ideal.mem_span_singleton_self ϖ)
    obtain ⟨b, hb⟩ := Ideal.mem_span_singleton'.mp (Ideal.span_singleton_pow ϖ 2 ▸
      hϖ.maximalIdeal_eq ▸ M.map_maximalIdeal_le (Ideal.mem_map_of_mem _ ht))
    refine ⟨stalkClosedPointToOfEq ((D.π ≫ M.τ) ≫ pullback.snd M.f M.f) (M.y default) hψ₂ b, ?_⟩
    rw [hΦd, hU₂d, ← stalkClosedPointToOfEq_germ _ _ hψ₂ _ hyU,
      ← stalkClosedPointToOfEq_germ _ _ hψ₃ _ hyU, hũ, stalkClosedPointToOfEq_congr
        (Category.assoc _ _ _).symm, stalkClosedPointToOfEq_comp _ _ _ hψ₂ _ hhy,
      CommRingCat.comp_apply, CommRingCat.comp_apply, ← hb, map_mul, map_pow, mul_comm]
  -- the functions vanish on the curves
  have hD : U₁ * (U₁ - Φ) ∈ specIdeal D.dD' := by
    rw [dD', specIdeal_reducedClosedι, PrimeSpectrum.mem_vanishingIdeal]
    rintro z (⟨g, hg⟩ | ⟨g, hg⟩)
    · refine Ideal.mul_mem_left _ _ (ΓSpecIso_hom_appLE_sub_mem_asIdeal (D.π ≫ M.τ)
        (pullback.fst M.f M.f) (pullback.snd M.f M.f ≫ M.h) ũ _ _ M.graph
        (by rw [graph_fst, graph_snd_assoc]) z ⟨pullback.fst M.graph M.τ g, ?_⟩)
      rw [← Hom.comp_apply, pullback.condition, Hom.comp_apply, hg, Hom.comp_apply]
    · refine Ideal.mul_mem_right _ _ ((ΓSpecIso_hom_appLE_mem_asIdeal_iff _ _ ũ z).mpr ?_)
      have hz : ((D.π ≫ M.τ) ≫ pullback.fst M.f M.f) z = M.y default := by
        rw [Hom.comp_apply, Hom.comp_apply, ← hg, ← Hom.comp_apply M.v, ← pullback.condition,
          Hom.comp_apply, ← Hom.comp_apply M.vertical, vertical_fst, Hom.comp_apply]
        exact congrArg _ (Subsingleton.elim _ _)
      rw [hz, mem_basicOpen _ _ _ hyU, hũ]
      exact hϖ.not_isUnit
  have hB : U₁ - U₂ ∈ specIdeal D.dB' := by
    rw [dB', specIdeal_reducedClosedι, PrimeSpectrum.mem_vanishingIdeal]
    rintro z ⟨g, hg⟩
    refine ΓSpecIso_hom_appLE_sub_mem_asIdeal (D.π ≫ M.τ) (pullback.fst M.f M.f)
      (pullback.snd M.f M.f) ũ _ _ (pullback.diagonal M.f)
      (by rw [pullback.diagonal_fst, pullback.diagonal_snd]) z
      ⟨pullback.fst (pullback.diagonal M.f) M.τ g, ?_⟩
    rw [← Hom.comp_apply, pullback.condition, Hom.comp_apply, hg, Hom.comp_apply]
  have hH : η₁ ∈ specIdeal D.dH' := by
    rw [dH', specIdeal_reducedClosedι, PrimeSpectrum.mem_vanishingIdeal]
    rintro z ⟨g, hg⟩
    have hz : ((D.π ≫ M.τ) ≫ pullback.snd M.f M.f) z = M.y default := by
      rw [Hom.comp_apply, Hom.comp_apply, ← hg, ← Hom.comp_apply M.hH, ← pullback.condition,
        Hom.comp_apply, ← Hom.comp_apply M.horizontal, horizontal_snd,
        Hom.comp_apply]
      exact congrArg _ (Subsingleton.elim _ _)
    have hU := (ΓSpecIso_hom_appLE_mem_asIdeal_iff _
      (preimage_eq_top_of_closedPoint_mem _ (hψ₂ ▸ hyU)).ge ũ z).mpr (by
      rw [hz, mem_basicOpen _ _ _ hyU, hũ]
      exact hϖ.not_isUnit)
    rw [← hU₂d, hU₂] at hU
    exact z.isPrime.mem_of_pow_mem _ ((Ideal.unit_mul_mem_iff_mem _ (hw.map j₂.hom)).mp hU)
  -- the initial forms
  have hw₁ : IsUnit (j₁ w) := hw.map j₁.hom
  have hw₂ : IsUnit (j₂ w) := hw.map j₂.hom
  have hf : U₁ * (U₁ - Φ) - j₁ w ^ 2 * ξ₁ ^ (2 * D.e) ∈
      maximalIdeal (strictHenselization D.s') ^ (2 * D.e + 1) := by
    obtain ⟨b, hb⟩ := hΦ
    rw [hb, hU₁, hU₂]
    have : j₁ w * ξ₁ ^ D.e * (j₁ w * ξ₁ ^ D.e - (j₂ w * η₁ ^ D.e) ^ 2 * b) -
        j₁ w ^ 2 * ξ₁ ^ (2 * D.e) = -(j₁ w * j₂ w ^ 2 * b) * (ξ₁ ^ D.e * η₁ ^ (2 * D.e)) := by
      ring
    rw [this]
    exact Ideal.mul_mem_left _ _ (Ideal.pow_le_pow_right (by have := D.one_le_e; omega)
      (monomial_mem_maximalIdeal_pow hξ₁ hη₁ _ _))
  refine ⟨tangentConesMeetAtOrigin_of_cusp (g := U₁ - U₂) (α := j₁ w) hm D.one_le_e
    (hw₁.pow 2) hw₂ hf ?_ hD hB,
    tangentConesMeetAtOrigin_of_axis (g := η₁) hm (hw₁.pow 2) isUnit_one hf ?_ hD hH⟩
  · rw [hU₁, hU₂, sub_self]
    exact zero_mem _
  · rw [one_mul, sub_self]
    exact zero_mem _

end AlgebraicGeometry.Etale.CurveLocalModel.CoverDatum
