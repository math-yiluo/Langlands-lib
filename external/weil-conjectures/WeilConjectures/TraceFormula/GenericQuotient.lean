/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.DenseAffineOpen
public import WeilConjectures.AlgebraicGeometry.GenericQuotient
public import WeilConjectures.AlgebraicGeometry.OverProduct
public import WeilConjectures.TraceFormula.ShriekTraceFunction

/-!
# Generic quotients of schemes by an automorphism of finite order

Let `X` be a nonempty separated scheme of finite type over a field `k` with an automorphism `e_X`
of finite order (`e_X^{m+1} = 𝟙`). This file shows that `X` is generically a finite étale cover of
a scheme with trivial automorphism (`AlgebraicGeometry.exists_isFinite_etale_of_pow_eq_refl`):
there are a nonempty `e_X`-stable open subscheme `U`, its reduction `Z`, and a finite étale
morphism `π : Z ⟶ V` to an affine scheme of finite type with `e_Z ≫ π = π` (SGA 1, Exposé V,
Prop. 1.1 and Cor. 2.4). The proof finds a nonempty `e_X`-stable affine open
(`AlgebraicGeometry.exists_nonempty_isAffineOpen_preimage_eq_self`, the intersection of the
translates of a dense affine open), presents it as `Spec B` with `e_X = Spec σ`
(`AlgebraicGeometry.exists_specAlgOver_isOpenImmersion`), and applies the affine case
`AlgebraicGeometry.exists_isFinite_etale_specAlgOver`.

It also records the powers of products of automorphisms and of the automorphism of the fixed locus
of `e_Y^{m+1}` (`AlgebraicGeometry.Scheme.overProdIso_pow`,
`AlgebraicGeometry.Scheme.fixedLocusIso_pow`).
-/

@[expose] public section

universe u

open CategoryTheory Limits TopologicalSpace

namespace CategoryTheory.Iso

/-- `e^{a+1} ≫ e^{b+1} = e^{a+b+2}`. -/
lemma pow_add_one {C : Type*} [Category C] {X : C} (e : X ≅ X) (a b : ℕ) :
    e.pow (a + b + 2) = e.pow (a + 1) ≪≫ e.pow (b + 1) := by
  induction b with
  | zero =>
    rw [zero_add, Iso.pow_one]
    rfl
  | succ b ih =>
    rw [show a + (b + 1) + 2 = a + b + 2 + 1 by omega, Iso.pow_succ e (a + b + 2), ih,
      Iso.pow_succ e (b + 1), Iso.trans_assoc]

end CategoryTheory.Iso

namespace AlgebraicGeometry

namespace Scheme

variable {S : Scheme.{u}}

lemma overProdIso_pow {W T : Over S} (e : W ≅ W) (e' : T ≅ T) (n : ℕ) :
    (overProdIso e e').pow (n + 1) = overProdIso (e.pow (n + 1)) (e'.pow (n + 1)) := by
  induction n with
  | zero => simp only [zero_add, Iso.pow_one]
  | succ n ih =>
    rw [Iso.pow_succ _ (n + 1), ih, Iso.pow_succ e (n + 1), Iso.pow_succ e' (n + 1),
      overProdIso_trans]

/-- The automorphism of the fixed locus of `e_Y^{m+1}` induced by `e_Y` has order dividing
`m + 1`. -/
lemma fixedLocusIso_pow {Y : Over S} (eY : Y ≅ Y) (m : ℕ) :
    (fixedLocusIso (eY.pow (m + 1)).hom eY
      (Iso.pow_hom_comp_eq_comp_pow_hom eY eY rfl m).symm).pow (m + 1) = Iso.refl _ := by
  ext1
  refine equalizer.hom_ext ?_
  rw [Iso.pow_hom_comp_eq_comp_pow_hom _ _ (fixedLocusIso_hom_ι _ _ _),
    ← equalizer.condition]
  simp

end Scheme

variable {k : Type u} [Field k]

/-- A nonempty separated scheme of finite type over `k` with an automorphism `e` of finite order
has a nonempty affine open subscheme stable under `e`: the intersection of the translates of a
dense affine open. -/
theorem exists_nonempty_isAffineOpen_preimage_eq_self (X : Over (Spec (.of k)))
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom] (eX : X ≅ X) {m : ℕ}
    (hm : eX.pow (m + 1) = Iso.refl X) [Nonempty X.left] :
    ∃ W : X.left.Opens, IsAffineOpen W ∧ (W : Set X.left).Nonempty ∧
      eX.hom.left ⁻¹ᵁ W = W := by
  have : IsLocallyNoetherian X.left := LocallyOfFiniteType.isLocallyNoetherian X.hom
  have : CompactSpace X.left := QuasiCompact.compactSpace_of_compactSpace X.hom
  have : IsNoetherian X.left := ⟨⟩
  have : IsSeparated (terminal.from X.left) := by
    rw [Subsingleton.elim (terminal.from X.left) (X.hom ≫ terminal.from _)]; infer_instance
  obtain ⟨V, hV, hVd⟩ := X.left.exists_isAffineOpen_dense
  let e : ℕ → (X.left ⟶ X.left) := fun n ↦ (eX.pow (n + 1)).hom.left
  have he : ∀ n, IsIso (e n) := fun n ↦
    inferInstanceAs (IsIso ((Over.forget _).map (eX.pow (n + 1)).hom))
  have hper : ∀ n, e (n + (m + 1)) = e n := fun n ↦ by
    simp only [e, ← add_assoc, Iso.pow_add_one, hm, Iso.trans_refl]
  have hshift : ∀ n, eX.hom.left ≫ e n = e (n + 1) := fun n ↦ by
    simp only [e]
    rw [Iso.pow_succ eX (n + 1), Iso.trans_hom, Iso.pow_hom_comp_eq_comp_pow_hom eX eX rfl n,
      Over.comp_left]
  let W : X.left.Opens := ⨅ i : Fin (m + 1), e i ⁻¹ᵁ V
  have hmem : ∀ x, x ∈ W ↔ ∀ n : ℕ, (e n).base x ∈ V := by
    intro x
    rw [← SetLike.mem_coe, Opens.coe_iInf, Set.mem_iInter]
    refine ⟨fun h n ↦ ?_, fun h i ↦ h i⟩
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      by_cases hn : n < m + 1
      · exact h ⟨n, hn⟩
      · obtain ⟨n', rfl⟩ := Nat.exists_eq_add_of_le (not_lt.1 hn)
        rw [add_comm, hper]
        exact ih n' (by omega)
  refine ⟨W, IsAffineOpen.iInf fun i ↦ hV.preimage_of_isIso (e i), ?_, ?_⟩
  · have hd : ∀ s : Finset (Fin (m + 1)),
        Dense (⋂ i ∈ s, ((e i ⁻¹ᵁ V : X.left.Opens) : Set X.left)) := by
      intro s
      induction s using Finset.induction_on with
      | empty => simp
      | insert a s ha ih =>
        rw [Finset.set_biInter_insert]
        refine Dense.inter_of_isOpen_left ?_ ih (e a ⁻¹ᵁ V).isOpen
        exact hVd.preimage (e a).isOpenMap
    have := hd Finset.univ
    simp only [Finset.mem_univ, Set.iInter_true] at this
    rw [Opens.coe_iInf]
    exact this.nonempty
  · ext x
    rw [SetLike.mem_coe, SetLike.mem_coe, Scheme.Hom.mem_preimage, hmem, hmem]
    refine ⟨fun h n ↦ ?_, fun h n ↦ ?_⟩
    · cases n with
      | zero =>
        have := h m
        rwa [← Scheme.Hom.comp_apply, hshift, show m + 1 = 0 + (m + 1) by omega, hper] at this
      | succ n => rw [← hshift, Scheme.Hom.comp_apply]; exact h n
    · rw [← Scheme.Hom.comp_apply, hshift]
      exact h (n + 1)

/-- A nonempty separated scheme of finite type over `k` with an automorphism `e` of finite order
contains a nonempty `e`-stable affine open subscheme `Spec B`, on which `e` is `Spec σ` for an
automorphism `σ` of the `k`-algebra `B` of finite order. -/
theorem exists_specAlgOver_isOpenImmersion (X : Over (Spec (.of k))) [LocallyOfFiniteType X.hom]
    [QuasiCompact X.hom] [IsSeparated X.hom] (eX : X ≅ X) {m : ℕ}
    (hm : eX.pow (m + 1) = Iso.refl X) [Nonempty X.left] :
    ∃ (B : Type u) (_ : CommRing B) (_ : Algebra k B) (_ : Algebra.FiniteType k B)
      (_ : Nontrivial B) (σ : B ≃ₐ[k] B) (_ : σ ^ (m + 1) = 1) (ι : specAlgOver B ⟶ X),
      IsOpenImmersion ι.left ∧ (specAlgOverIso σ).hom ≫ ι = ι ≫ eX.hom := by
  have appLE_of_eq : ∀ {Y : Scheme.{u}} {f g : X.left ⟶ Y} (h : f = g) {U : Y.Opens}
      {V : X.left.Opens} (e : V ≤ f ⁻¹ᵁ U), f.appLE U V e = g.appLE U V (h ▸ e) := by
    intro Y f g h U V e; subst h; rfl
  have appLE_id : ∀ {V : X.left.Opens} (e : V ≤ (𝟙 X.left) ⁻¹ᵁ V),
      (𝟙 X.left : X.left ⟶ X.left).appLE V V e = 𝟙 _ := by
    intro V e
    simp only [Scheme.Hom.appLE, Scheme.Hom.id_app, Category.id_comp]
    exact X.left.presheaf.map_id _
  obtain ⟨W, hW, hWne, hWst⟩ := exists_nonempty_isAffineOpen_preimage_eq_self X eX hm
  have hle : ∀ n, (eX.pow (n + 1)).hom.left ⁻¹ᵁ W = W := by
    intro n
    induction n with
    | zero => simpa using hWst
    | succ n ih =>
      rw [Iso.pow_succ eX (n + 1), Iso.trans_hom, Over.comp_left, Scheme.Hom.comp_preimage, hWst,
          ih]
  have hle' : eX.inv.left ⁻¹ᵁ W = W := by
    conv_lhs => rw [← hWst]
    rw [← Scheme.Hom.comp_preimage, ← Over.comp_left, Iso.inv_hom_id, Over.id_left,
      Scheme.Hom.id_preimage]
  let φ : CommRingCat.of k ⟶ Γ(X.left, W) := (Scheme.ΓSpecIso (.of k)).inv ≫ X.hom.appLE ⊤ W le_top
  let : Algebra k Γ(X.left, W) := φ.hom.toAlgebra
  let s : Γ(X.left, W) ⟶ Γ(X.left, W) := eX.hom.left.appLE W W hWst.ge
  let t : Γ(X.left, W) ⟶ Γ(X.left, W) := eX.inv.left.appLE W W hle'.ge
  have hst : s ≫ t = 𝟙 Γ(X.left, W) := by
    rw [Scheme.Hom.appLE_comp_appLE, appLE_of_eq (g := 𝟙 X.left) (by
      rw [← Over.comp_left, Iso.inv_hom_id, Over.id_left]), appLE_id]
  have hts : t ≫ s = 𝟙 Γ(X.left, W) := by
    rw [Scheme.Hom.appLE_comp_appLE, appLE_of_eq (g := 𝟙 X.left) (by
      rw [← Over.comp_left, Iso.hom_inv_id, Over.id_left]), appLE_id]
  have hφs : φ ≫ s = φ := by
    rw [Category.assoc, Scheme.Hom.appLE_comp_appLE,
      appLE_of_eq (Over.w eX.hom)]
  let σ : Γ(X.left, W) ≃ₐ[k] Γ(X.left, W) :=
    AlgEquiv.ofRingEquiv (f := RingEquiv.ofRingHom s.hom t.hom
      (congrArg CommRingCat.Hom.hom hts) (congrArg CommRingCat.Hom.hom hst))
      (fun r ↦ congrArg (fun f : CommRingCat.of k ⟶ Γ(X.left, W) ↦ f.hom r) hφs)
  have hσs : ∀ x, σ x = s.hom x := fun _ ↦ rfl
  have hkey : ∀ n, (eX.pow (n + 2)).hom.left.appLE W W (hle (n + 1)).ge =
      s ≫ (eX.pow (n + 1)).hom.left.appLE W W (hle n).ge := by
    intro n
    rw [Scheme.Hom.appLE_comp_appLE]
    exact appLE_of_eq (by rw [Iso.pow_succ eX (n + 1), Iso.trans_hom, Over.comp_left]) _
  have hpow : ∀ n (x : Γ(X.left, W)), (σ ^ (n + 1)) x =
      ((eX.pow (n + 1)).hom.left.appLE W W (hle n).ge).hom x := by
    intro n
    induction n with
    | zero =>
      intro x
      rw [appLE_of_eq (g := eX.hom.left) (by rw [zero_add, Iso.pow_one]) (hle 0).ge]
      change (σ ^ 1) x = _
      rw [pow_one, hσs]
    | succ n ih =>
      intro x
      rw [pow_succ, AlgEquiv.mul_apply, ih]
      rw [hkey, CommRingCat.hom_comp, RingHom.comp_apply, hσs]
  have : Nonempty W := hWne.to_subtype
  refine ⟨Γ(X.left, W), inferInstance, inferInstance, ?_, inferInstance, σ, ?_,
    Over.homMk hW.fromSpec ?_, ?_, ?_⟩
  · have hft : (X.hom.appLE ⊤ W le_top).hom.FiniteType :=
      HasRingHomProperty.appLE @LocallyOfFiniteType X.hom ‹_› ⟨⊤, isAffineOpen_top _⟩ ⟨W, hW⟩ _
    exact hft.comp (RingHom.FiniteType.of_surjective _
      (Scheme.ΓSpecIso (.of k)).commRingCatIsoToRingEquiv.symm.surjective)
  · ext x
    rw [hpow, AlgEquiv.one_apply, appLE_of_eq (g := 𝟙 X.left) (by
      rw [hm, Iso.refl_hom, Over.id_left]), appLE_id]
    rfl
  · dsimp only [specAlgOver, Over.mk_hom]
    rw [← IsAffineOpen.SpecMap_appLE_fromSpec X.hom (isAffineOpen_top _) hW le_top,
      IsAffineOpen.fromSpec_top,
      Scheme.isoSpec_Spec_inv, ← Spec.map_comp]
    rfl
  · exact inferInstanceAs (IsOpenImmersion hW.fromSpec)
  · refine Over.OverMorphism.ext ?_
    simp only [Over.comp_left, specAlgOverIso_hom, specAlgOverMap_left]
    exact IsAffineOpen.SpecMap_appLE_fromSpec eX.hom.left hW hW hWst.ge


/-- **Generic quotient by an automorphism of finite order** (SGA 1, Exposé V, Prop. 1.1 and
Cor. 2.4). Let `X` be a nonempty separated scheme of finite type over `k` with an automorphism
`e_X` of finite order. There are a nonempty `e_X`-stable open subscheme `j : U ⟶ X`, a surjective
closed immersion `i : Z ⟶ U` (the reduction of `U`) stable under an automorphism `e_Z`, and a
finite étale morphism `π : Z ⟶ V` to an affine scheme of finite type over `k` with
`e_Z ≫ π = π`. -/
theorem exists_isFinite_etale_of_pow_eq_refl (X : Over (Spec (.of k)))
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom] (eX : X ≅ X) {m : ℕ}
    (hm : eX.pow (m + 1) = Iso.refl X) [Nonempty X.left] :
    ∃ (U : Over (Spec (.of k))) (_ : LocallyOfFiniteType U.hom) (_ : QuasiCompact U.hom)
      (_ : IsSeparated U.hom) (eU : U ≅ U) (j : U ⟶ X) (_ : IsOpenImmersion j.left)
      (_ : eU.hom ≫ j = j ≫ eX.hom) (Z : Over (Spec (.of k))) (_ : LocallyOfFiniteType Z.hom)
      (_ : QuasiCompact Z.hom) (_ : IsSeparated Z.hom) (eZ : Z ≅ Z) (i : Z ⟶ U)
      (_ : IsClosedImmersion i.left) (_ : eZ.hom ≫ i = i ≫ eU.hom) (V : Over (Spec (.of k)))
      (_ : IsAffine V.left) (_ : LocallyOfFiniteType V.hom) (π : Z ⟶ V) (_ : IsFinite π.left)
      (_ : Etale π.left),
      Nonempty U.left ∧ Function.Surjective i.left.base ∧ eZ.hom ≫ π = π := by
  obtain ⟨B, _, _, _, _, σ, hσ, ι, hι, hιe⟩ := exists_specAlgOver_isOpenImmersion X eX hm
  obtain ⟨U, _, _, _, eU, j, _, hj, Z, _, _, _, eZ, i, _, hi, V, _, _, π, _, _, hU, hsurj, hπ⟩ :=
    exists_isFinite_etale_specAlgOver B σ hσ
  have : IsOpenImmersion (j ≫ ι).left := by rw [Over.comp_left]; infer_instance
  refine ⟨U, inferInstance, inferInstance, inferInstance, eU, j ≫ ι, this, ?_, Z, inferInstance,
    inferInstance, inferInstance, eZ, i, inferInstance, hi, V, inferInstance, inferInstance, π,
    inferInstance, inferInstance, hU, hsurj, hπ⟩
  rw [reassoc_of% hj, hιe, Category.assoc]

end AlgebraicGeometry
