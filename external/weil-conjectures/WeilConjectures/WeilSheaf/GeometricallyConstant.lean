/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.DeligneLaumon.AffineLine.Defs
public import WeilConjectures.SixFunctors.ProEtale.Adic.TrivialRepresentation
public import WeilConjectures.WeilSheaf.GeometricCoinvariants

/-!
# Irreducible geometrically constant Weil sheaves are constant twists

Let `F` be an irreducible lisse Weil sheaf on a `k₀`-scheme `U` with connected geometric fiber
`Ū`, and suppose that `F` is geometrically constant: its underlying sheaf `F̄` is isomorphic to
`ℚ̄_ℓⁿ` on `Ū`. Then `F` is a constant Weil twist `ℚ̄_ℓ(b)` of the constant Weil sheaf
(`AlgebraicGeometry.WeilSheaf.exists_iso_constantTwist_of_isGeometricallyConstant`).

Indeed the global sections `Γ(Ū, F̄) ≅ ℚ̄_ℓⁿ` are a nonzero finite-dimensional `ℚ̄_ℓ`-vector
space, so the Frobenius has an eigenvector `a` with eigenvalue `b`, `ℚ̄_ℓ` being algebraically
closed. The morphism `ℚ̄_ℓ ⟶ F̄` sending `1` to `a` is a morphism of Weil sheaves
`ℚ̄_ℓ(b) ⟶ F` (`AlgebraicGeometry.WeilSheaf.homOfGlobalSection`). It is a split monomorphism of
sheaves: on the connected `Ū` a nonzero morphism `ℚ̄_ℓ ⟶ ℚ̄_ℓⁿ` is a nonzero column of
constants (`AlgebraicGeometry.ProEtale.AdicSheaf.mono_of_ne_zero`). By irreducibility of
`F` it is an isomorphism.
-/

@[expose] public section

universe u

open CategoryTheory Limits

attribute [local instance] Abelian.hasFiniteBiproducts

namespace AlgebraicGeometry

namespace ProEtale.AdicSheaf

variable {l : ℕ} [Fact l.Prime] {Z : Scheme.{u}}

/-- On a connected scheme, a nonzero endomorphism of the unit `ℚ̄_ℓ` is an isomorphism: it is the
multiplication by a nonzero constant. -/
lemma isIso_of_ne_zero [ConnectedSpace Z] {ψ : unit l Z ⟶ unit l Z} (hψ : ψ ≠ 0) : IsIso ψ := by
  have x : Z := Classical.arbitrary Z
  set c := (unitEndFun ψ).1 x with hc
  have hψc : unitEndFun ψ = algebraMap _ _ c :=
    PadicAlgCl.locallyFiniteFunctions_eq_algebraMap _ x
  have hc0 : c ≠ 0 := by
    intro h0
    apply hψ
    apply unitEndFun_injective
    rw [hψc, h0, map_zero, unitEndFun_zero]
  let ψ' := unitMul (l := l) (V := Z) (algebraMap _ _ c⁻¹)
  refine ⟨ψ', unitEndFun_injective ?_, unitEndFun_injective ?_⟩
  · rw [unitEndFun_comp, unitEndFun_unitMul, hψc, ← map_mul, mul_inv_cancel₀ hc0, map_one,
      unitEndFun_id]
  · rw [unitEndFun_comp, unitEndFun_unitMul, hψc, ← map_mul, inv_mul_cancel₀ hc0, map_one,
      unitEndFun_id]

/-- On a connected scheme, a nonzero morphism `ℚ̄_ℓ ⟶ M` into a sheaf `M ≅ ℚ̄_ℓⁿ` is a
monomorphism: one of its coordinates is a nonzero constant, hence invertible. -/
lemma mono_of_ne_zero [ConnectedSpace Z] {M : AdicSheaf l Z} {n : ℕ}
    (e : M ≅ ⨁ fun _ : Fin n ↦ unit l Z) {v : unit l Z ⟶ M} (hv : v ≠ 0) : Mono v := by
  have : ∃ j, v ≫ e.hom ≫ biproduct.π _ j ≠ 0 := by
    by_contra! h
    apply hv
    rw [← cancel_mono e.hom, zero_comp]
    exact biproduct.hom_ext _ _ fun j ↦ by simpa using h j
  obtain ⟨j, hj⟩ := this
  have := isIso_of_ne_zero hj
  exact mono_of_mono v (e.hom ≫ biproduct.π _ j)

end ProEtale.AdicSheaf

namespace WeilSheaf

open ProEtale

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]
variable {U : Scheme.{u}} [U.Over (Spec (CommRingCat.of k₀))]

/-- If the geometric fiber `Ū` is connected, the underlying sheaf of a geometrically constant
Weil sheaf is isomorphic to `ℚ̄_ℓⁿ` on all of `Ū`. -/
theorem IsGeometricallyConstant.exists_iso_biproduct_unit
    [ConnectedSpace (U ↘ Spec (CommRingCat.of k₀)).geometricFiber] {F : WeilSheaf k₀ l U}
    (hc : F.IsGeometricallyConstant) :
    ∃ n : ℕ, Nonempty (F.obj.carrier ≅
      ⨁ fun _ : Fin n ↦ AdicSheaf.unit l (U ↘ Spec (CommRingCat.of k₀)).geometricFiber) := by
  set Ū := (U ↘ Spec (CommRingCat.of k₀)).geometricFiber
  have : ConnectedSpace (⊤ : Ū.Opens) :=
    Subtype.connectedSpace (by simpa using isConnected_univ (α := Ū))
  obtain ⟨n, ⟨e₀⟩⟩ := hc ⊤ this
  have : IsIso (⊤ : Ū.Opens).ι := inferInstanceAs (IsIso Ū.topIso.hom)
  let P := ((⊤ : Ū.Opens).ι)^*ᵃ[l]
  refine ⟨n, ⟨P.preimageIso (e₀ ≪≫ (biproduct.mapIso fun _ ↦
    adicUpperStarUnitIso l (⊤ : Ū.Opens).ι).symm ≪≫ (P.mapBiproduct _).symm)⟩⟩

/-- **Irreducible geometrically constant Weil sheaves are constant twists.** An irreducible
lisse Weil sheaf `F` on `U` with connected geometric fiber `Ū` whose underlying sheaf is
constant is isomorphic to a constant Weil twist `ℚ̄_ℓ(b)` of the constant Weil sheaf. The
Frobenius has an eigenvector `a` on the nonzero global sections `Γ(Ū, F̄)`; the corresponding
morphism `ℚ̄_ℓ(b) ⟶ F` is a monomorphism, hence an isomorphism by irreducibility. -/
theorem exists_iso_constantTwist_of_isGeometricallyConstant
    [LocallyOfFiniteType (U ↘ Spec (CommRingCat.of k₀))]
    [QuasiCompact (U ↘ Spec (CommRingCat.of k₀))]
    [ConnectedSpace (U ↘ Spec (CommRingCat.of k₀)).geometricFiber]
    {F : WeilSheaf k₀ l U} (hF : F.IsIrreducibleLisse) (hc : F.IsGeometricallyConstant) :
    ∃ b : (PadicAlgCl l)ˣ, Nonempty (F ≅ (adicConstant k₀ l U).constantTwist b) := by
  set Ū := (U ↘ Spec (CommRingCat.of k₀)).geometricFiber
  obtain ⟨n, ⟨e⟩⟩ := hc.exists_iso_biproduct_unit
  have hunit : ¬ IsZero (AdicSheaf.unit l Ū) := fun h ↦
    not_isZero_adicConstantSheaf l _ ((AdicSheaf.forget _).map_isZero h)
  -- the dimension `n` is positive, `F` being nonzero
  have hn : 0 < n := by
    refine Nat.pos_of_ne_zero fun hn ↦ hF.2.1 (isZero_iff_isZero_carrier.2 ?_)
    subst hn
    exact ((IsZero.iff_id_eq_zero _).2 (biproduct.hom_ext _ _ fun j ↦ j.elim0)).of_iso e
  -- a nonzero global section of `F̄`
  let v₀ : AdicSheaf.unit l Ū ⟶ F.obj.carrier :=
    biproduct.ι (fun _ : Fin n ↦ AdicSheaf.unit l Ū) ⟨0, hn⟩ ≫ e.inv
  have hv₀ : v₀ ≠ 0 := by
    have h1 : v₀ ≫ e.hom ≫ biproduct.π _ ⟨0, hn⟩ = 𝟙 _ := by
      simp only [v₀, Category.assoc, Iso.inv_hom_id_assoc]
      exact biproduct.ι_π_self _ _
    intro h
    rw [h, zero_comp] at h1
    exact hunit ((IsZero.iff_id_eq_zero _).2 h1.symm)
  have : Nontrivial F.globalSections.carrier := by
    refine ⟨⟨globalSectionOfModHom v₀, 0, fun h ↦ hv₀ ?_⟩⟩
    refine (bijective_globalSectionOfModHom F.obj.carrier).1 (h.trans ?_)
    rw [globalSectionOfModHom_eq]
    erw [Mod.zero_hom, Functor.map_zero]
    rfl
  -- a Frobenius eigenvector `a` with eigenvalue `β`
  obtain ⟨β, hβ⟩ := Module.End.exists_eigenvalue F.globalSections.frobeniusEnd
  obtain ⟨a, ha⟩ := hβ.exists_hasEigenvector
  rw [Module.End.hasEigenvector_iff, Module.End.mem_eigenspace_iff] at ha
  obtain ⟨ha, ha₀⟩ := ha
  have hβ₀ : β ≠ 0 := by
    rintro rfl
    rw [zero_smul] at ha
    exact ha₀ (F.globalSections.frobenius.injective (ha.trans (map_zero _).symm))
  let b := Units.mk0 β hβ₀
  let i := homOfGlobalSection F b a ha
  have hi : i ≠ 0 := homOfGlobalSection_ne_zero F b a ha ha₀
  have hv : modHomOfGlobalSection F a ≠ 0 := fun h ↦ ha₀ (by
    rw [← globalSectionOfModHom_modHomOfGlobalSection F a, h, globalSectionOfModHom_eq]
    erw [Mod.zero_hom, Functor.map_zero]
    rfl)
  have : Mono i :=
    ((WeilSheaf.objectProperty k₀ l U).ι ⋙ Endofunctor.IsoAlgebra.forget
      (WeilSheaf.frobeniusPullback k₀ l U)).mono_of_mono_map (AdicSheaf.mono_of_ne_zero e hv)
  obtain h | h := hF.2.2 _ i this ((isLisse_adicConstant k₀ l U).constantTwist)
  · exact absurd (h.eq_of_src i 0) hi
  · exact ⟨b, ⟨(asIso i).symm⟩⟩

/-- **Weil sheaves with constant rank-one underlying sheaf are constant twists.** A Weil sheaf `F`
on `U` with connected geometric fiber `Ū` whose underlying sheaf is isomorphic to `ℚ̄_ℓ` is
isomorphic to a constant Weil twist `ℚ̄_ℓ(b)`: a Frobenius eigenvector `a` of the global sections
gives a morphism `ℚ̄_ℓ(b) ⟶ F` whose underlying morphism `ℚ̄_ℓ ⟶ F̄ ≅ ℚ̄_ℓ` is nonzero, hence an
isomorphism on the connected `Ū`. -/
theorem exists_iso_constantTwist_of_iso_unit
    [LocallyOfFiniteType (U ↘ Spec (CommRingCat.of k₀))]
    [QuasiCompact (U ↘ Spec (CommRingCat.of k₀))]
    [ConnectedSpace (U ↘ Spec (CommRingCat.of k₀)).geometricFiber] {F : WeilSheaf k₀ l U}
    (e : F.obj.carrier ≅ AdicSheaf.unit l (U ↘ Spec (CommRingCat.of k₀)).geometricFiber) :
    ∃ b : (PadicAlgCl l)ˣ, Nonempty (F ≅ (adicConstant k₀ l U).constantTwist b) := by
  set Ū := (U ↘ Spec (CommRingCat.of k₀)).geometricFiber
  have hunit : ¬ IsZero (AdicSheaf.unit l Ū) := fun h ↦
    not_isZero_adicConstantSheaf l _ ((AdicSheaf.forget _).map_isZero h)
  have hv₀ : e.inv ≠ 0 := fun h ↦ hunit ((IsZero.iff_id_eq_zero _).2 (by
    rw [← e.inv_hom_id, h, zero_comp]))
  have : Nontrivial F.globalSections.carrier := by
    refine ⟨⟨globalSectionOfModHom e.inv, 0, fun h ↦ hv₀ ?_⟩⟩
    refine (bijective_globalSectionOfModHom F.obj.carrier).1 (h.trans ?_)
    rw [globalSectionOfModHom_eq]
    erw [Mod.zero_hom, Functor.map_zero]
    rfl
  -- a Frobenius eigenvector `a` with eigenvalue `β`
  obtain ⟨β, hβ⟩ := Module.End.exists_eigenvalue F.globalSections.frobeniusEnd
  obtain ⟨a, ha⟩ := hβ.exists_hasEigenvector
  rw [Module.End.hasEigenvector_iff, Module.End.mem_eigenspace_iff] at ha
  obtain ⟨ha, ha₀⟩ := ha
  have hβ₀ : β ≠ 0 := by
    rintro rfl
    rw [zero_smul] at ha
    exact ha₀ (F.globalSections.frobenius.injective (ha.trans (map_zero _).symm))
  let b := Units.mk0 β hβ₀
  let i := homOfGlobalSection F b a ha
  have hv : modHomOfGlobalSection F a ≠ 0 := fun h ↦ ha₀ (by
    rw [← globalSectionOfModHom_modHomOfGlobalSection F a, h, globalSectionOfModHom_eq]
    erw [Mod.zero_hom, Functor.map_zero]
    rfl)
  -- its underlying morphism `ℚ̄_ℓ ⟶ F̄ ≅ ℚ̄_ℓ` is a nonzero constant, hence invertible
  have : IsIso (modHomOfGlobalSection F a ≫ e.hom) := AdicSheaf.isIso_of_ne_zero fun h ↦ hv (by
    rw [← Category.comp_id (modHomOfGlobalSection F a), ← e.hom_inv_id, ← Category.assoc, h,
      zero_comp])
  have : IsIso (modHomOfGlobalSection F a) := IsIso.of_isIso_comp_right _ e.hom
  have : IsIso ((Endofunctor.IsoAlgebra.forget (WeilSheaf.frobeniusPullback k₀ l U)).map
      ((WeilSheaf.objectProperty k₀ l U).ι.map i)) := this
  have : IsIso ((WeilSheaf.objectProperty k₀ l U).ι.map i) :=
    isIso_of_reflects_iso _ (Endofunctor.IsoAlgebra.forget _)
  have : IsIso i := (ObjectProperty.fullyFaithfulι _).isIso_of_isIso_map i
  exact ⟨b, ⟨(asIso i).symm⟩⟩

end WeilSheaf

end AlgebraicGeometry
