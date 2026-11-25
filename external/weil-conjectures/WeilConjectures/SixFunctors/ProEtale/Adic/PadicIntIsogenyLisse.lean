/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.Mathlib.CategoryTheory.Abelian.Basic
public import WeilConjectures.Mathlib.CategoryTheory.Abelian.FunctorCategory
public import WeilConjectures.Mathlib.CategoryTheory.Preadditive.FunctorCategory
public import WeilConjectures.SixFunctors.ProEtale.Adic.LisseInternalHom
public import WeilConjectures.SixFunctors.ProEtale.Adic.PadicIntLatticeLisse

/-!
# Rationalisation inverts bounded isogenies of `ℤ_ℓ,X`-modules

Extension of scalars `M ↦ ℚ̄_ℓ ⊗_{ℤ_ℓ} M` from `ℤ_ℓ,X`-modules to `ℓ`-adic sheaves on `X_proét`
kills bounded torsion, `ℓ` being invertible in `ℚ̄_ℓ`. We deduce that `ℓ`-adic towers up to
bounded torsion (in the sense of Artin–Rees) have lisse rationalised limits.

## Main results

- `AlgebraicGeometry.ProEtale.isIso_zsmul_id_adicSheaf`: multiplication by a nonzero integer is
  an automorphism of every `ℓ`-adic sheaf.
- `AlgebraicGeometry.ProEtale.isZero_adicSheafExtendScalars_obj_of_zsmul_id_eq_zero`: the
  rationalisation of a `ℤ_ℓ,X`-module of bounded torsion is zero.
- `AlgebraicGeometry.ProEtale.isIso_adicSheafExtendScalars_map_of_zsmul_kernel_ι_eq_zero`:
  rationalisation inverts morphisms whose kernel and cokernel have bounded torsion.
- `ProEtale.isIso_adicSheafExtendScalars_map_limMap_of_zsmul_kernel_ι_app_eq_zero`:
  the same for limits of morphisms of diagrams with uniformly bounded torsion kernels and
  cokernels.
- `AlgebraicGeometry.ProEtale.isAdicLisseSheaf_adicSheafExtendScalars_limit_of_hom` and
  `AlgebraicGeometry.ProEtale.isAdicLisseSheaf_adicSheafExtendScalars_limit_of_hom'`: a tower
  related to an `ℓ`-adic tower of rank `r` by a morphism of towers with uniformly bounded torsion
  kernels and cokernels has lisse rationalised limit.
- `AlgebraicGeometry.ProEtale.isAdicLisseSheaf_adicSheafExtendScalars_limit_shift_iff`: shifting
  the indices of a tower does not change its rationalised limit.
- `AlgebraicGeometry.ProEtale.isAdicLisseSheaf_adicSheafExtendScalars_of_cover_of_hom`: a
  `ℤ_ℓ,X`-module pro-étale locally related to a free module of finite rank by a morphism with
  bounded torsion kernel and cokernel (e.g. locally `ℤ_ℓ^r ⊕ T` with `T` of bounded torsion) has
  lisse rationalisation.
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory MonObj Limits Opposite

namespace AlgebraicGeometry.ProEtale

open Scheme

attribute [local instance] Sheaf.monoidalCategory

/-- In the category of modules over a commutative ring in which the integer `n` is invertible,
multiplication by `n` is an isomorphism. -/
lemma isIso_zsmul_id_moduleCat {R : Type*} [CommRing R] (M : ModuleCat R) {n : ℤ}
    (hn : IsUnit (n : R)) : IsIso (n • 𝟙 M) := by
  refine ⟨ModuleCat.ofHom (hn.unit⁻¹.val • LinearMap.id), ?_, ?_⟩ <;>
  · ext x
    simp [← Int.cast_smul_eq_zsmul R n, smul_smul]

variable (l : ℕ) [Fact l.Prime] {X : Scheme.{u}}

/-- Multiplication by a nonzero integer is an automorphism of every `ℓ`-adic sheaf, `ℚ̄_ℓ` being a
field of characteristic zero. -/
lemma isIso_zsmul_id_adicSheaf (F : AdicSheaf l X) {n : ℤ} (hn : n ≠ 0) : IsIso (n • 𝟙 F) := by
  rw [← isIso_iff_of_reflects_iso _ (Mod.forget _),
    ← isIso_iff_of_reflects_iso _ (sheafToPresheaf _ _), Functor.map_zsmul, Functor.map_zsmul,
    CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id]
  refine @NatIso.isIso_of_isIso_app _ _ _ _ _ _ _ fun U ↦ ?_
  rw [NatTrans.app_zsmul, NatTrans.id_app]
  exact isIso_zsmul_id_moduleCat _ (by
    simpa using ((isUnit_iff_ne_zero (a := (n : PadicAlgCl l))).2 (by simpa using hn)).map
      (ULift.ringEquiv.{_, u + 1} (R := PadicAlgCl l)).symm)

/-- **Rationalisation inverts isogenies**: if `φ : M ⟶ N` and `ψ : N ⟶ M` are morphisms of
`ℤ_ℓ,X`-modules whose composites are multiplication by a nonzero integer `n`, then
`ℚ̄_ℓ ⊗ φ` is an isomorphism of `ℓ`-adic sheaves. -/
lemma isIso_adicSheafExtendScalars_map_of_comp_eq_zsmul
    {M N : Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) (padicIntAbSheaf X l)} (φ : M ⟶ N)
    (ψ : N ⟶ M) {n : ℤ} (hn : n ≠ 0) (h₁ : φ ≫ ψ = n • 𝟙 M) (h₂ : ψ ≫ φ = n • 𝟙 N) :
    IsIso ((adicSheafExtendScalars X l).map φ) := by
  have : IsIso ((adicSheafExtendScalars X l).map φ ≫ (adicSheafExtendScalars X l).map ψ) := by
    rw [← Functor.map_comp, h₁, Functor.map_zsmul, CategoryTheory.Functor.map_id]
    exact isIso_zsmul_id_adicSheaf l _ hn
  have : IsIso ((adicSheafExtendScalars X l).map ψ ≫ (adicSheafExtendScalars X l).map φ) := by
    rw [← Functor.map_comp, h₂, Functor.map_zsmul, CategoryTheory.Functor.map_id]
    exact isIso_zsmul_id_adicSheaf l _ hn
  have := mono_of_mono ((adicSheafExtendScalars X l).map φ) ((adicSheafExtendScalars X l).map ψ)
  have := epi_of_epi ((adicSheafExtendScalars X l).map ψ) ((adicSheafExtendScalars X l).map φ)
  exact isIso_of_mono_of_epi _

/-- **Rationalisation kills bounded torsion**: the extension of scalars `ℚ̄_ℓ ⊗ M` of a
`ℤ_ℓ,X`-module `M` killed by a nonzero integer is zero. -/
lemma isZero_adicSheafExtendScalars_obj_of_zsmul_id_eq_zero
    (M : Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) (padicIntAbSheaf X l)) {n : ℤ} (hn : n ≠ 0)
    (h : n • 𝟙 M = 0) : IsZero ((adicSheafExtendScalars X l).obj M) := by
  have := isIso_zsmul_id_adicSheaf l ((adicSheafExtendScalars X l).obj M) hn
  rw [← CategoryTheory.Functor.map_id, ← Functor.map_zsmul, h, Functor.map_zero] at this
  exact IsZero.of_mono_zero _ ((adicSheafExtendScalars X l).obj M)

/-- **Rationalisation inverts morphisms with bounded torsion kernel and cokernel**: if the kernel
of a morphism `φ` of `ℤ_ℓ,X`-modules is killed by a nonzero integer `a` and its cokernel by a
nonzero integer `b`, then `ℚ̄_ℓ ⊗ φ` is an isomorphism of `ℓ`-adic sheaves. -/
lemma isIso_adicSheafExtendScalars_map_of_zsmul_kernel_ι_eq_zero
    {M N : Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) (padicIntAbSheaf X l)} (φ : M ⟶ N)
    {a b : ℤ} (ha₀ : a ≠ 0) (hb₀ : b ≠ 0) (ha : a • kernel.ι φ = 0)
    (hb : b • cokernel.π φ = 0) :
    IsIso ((adicSheafExtendScalars X l).map φ) := by
  obtain ⟨ψ, h₁, h₂⟩ := Abelian.exists_comp_eq_zsmul_id_of_zsmul_kernel_ι_eq_zero φ ha hb
  exact isIso_adicSheafExtendScalars_map_of_comp_eq_zsmul l φ ψ (mul_ne_zero ha₀ hb₀) h₁ h₂

/-- **Rationalisation is invariant under bounded isogenies**: if the kernel of a morphism `φ` of
`ℤ_ℓ,X`-modules is killed by a nonzero integer `a` and its cokernel by a nonzero integer `b`,
then `ℚ̄_ℓ ⊗ M` is lisse if and only if `ℚ̄_ℓ ⊗ N` is. -/
theorem isAdicLisseSheaf_adicSheafExtendScalars_iff_of_zsmul_kernel_ι_eq_zero
    {M N : Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) (padicIntAbSheaf X l)} (φ : M ⟶ N)
    {a b : ℤ} (ha₀ : a ≠ 0) (hb₀ : b ≠ 0) (ha : a • kernel.ι φ = 0)
    (hb : b • cokernel.π φ = 0) :
    IsAdicLisseSheaf ((adicSheafExtendScalars X l).obj M) ↔
      IsAdicLisseSheaf ((adicSheafExtendScalars X l).obj N) :=
  have := isIso_adicSheafExtendScalars_map_of_zsmul_kernel_ι_eq_zero l φ ha₀ hb₀ ha hb
  ⟨IsAdicLisseSheaf.of_iso (asIso ((adicSheafExtendScalars X l).map φ)),
    IsAdicLisseSheaf.of_iso (asIso ((adicSheafExtendScalars X l).map φ)).symm⟩

/-- **Rationalisation of limits inverts levelwise bounded isogenies**: let `φ : G ⟶ H` be a
morphism of diagrams of `ℤ_ℓ,X`-modules whose components have kernels killed by a fixed nonzero
integer `a` and cokernels killed by a fixed nonzero integer `b`. Then `ℚ̄_ℓ ⊗ lim φ` is an
isomorphism. Indeed `φ` has a quasi-inverse up to `a * b` in the functor category
(`CategoryTheory.Abelian.exists_comp_eq_zsmul_id_of_zsmul_kernel_ι_eq_zero`), hence so does
`lim φ`. -/
lemma isIso_adicSheafExtendScalars_map_limMap_of_zsmul_kernel_ι_app_eq_zero
    {J : Type*} [Category J]
    {G H : J ⥤ Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) (padicIntAbSheaf X l)}
    [HasLimit G] [HasLimit H] (φ : G ⟶ H) {a b : ℤ} (ha₀ : a ≠ 0) (hb₀ : b ≠ 0)
    (ha : ∀ j, a • kernel.ι (φ.app j) = 0) (hb : ∀ j, b • cokernel.π (φ.app j) = 0) :
    IsIso ((adicSheafExtendScalars X l).map (limMap φ)) := by
  obtain ⟨ψ, h₁, h₂⟩ := Abelian.exists_comp_eq_zsmul_id_of_zsmul_kernel_ι_eq_zero φ
    (Abelian.FunctorCategory.zsmul_kernel_ι_eq_zero_of_app φ ha)
    (Abelian.FunctorCategory.zsmul_cokernel_π_eq_zero_of_app φ hb)
  refine isIso_adicSheafExtendScalars_map_of_comp_eq_zsmul l (limMap φ) (limMap ψ)
    (mul_ne_zero ha₀ hb₀) (limit.hom_ext fun j ↦ ?_) (limit.hom_ext fun j ↦ ?_)
  · rw [Category.assoc, limMap_π, limMap_π_assoc, ← NatTrans.comp_app, h₁, NatTrans.app_zsmul,
      NatTrans.id_app, Preadditive.comp_zsmul, Category.comp_id, Preadditive.zsmul_comp,
      Category.id_comp]
  · rw [Category.assoc, limMap_π, limMap_π_assoc, ← NatTrans.comp_app, h₂, NatTrans.app_zsmul,
      NatTrans.id_app, Preadditive.comp_zsmul, Category.comp_id, Preadditive.zsmul_comp,
      Category.id_comp]

/-- **Lisseness of rationalised limits is invariant under levelwise bounded isogenies**: for a
morphism `φ : G ⟶ H` of diagrams of `ℤ_ℓ,X`-modules whose components have kernels killed by a
fixed nonzero integer `a` and cokernels killed by a fixed nonzero integer `b`, `ℚ̄_ℓ ⊗ lim G` is
lisse if and only if `ℚ̄_ℓ ⊗ lim H` is. -/
theorem isAdicLisseSheaf_adicSheafExtendScalars_limit_iff_of_zsmul_kernel_ι_app_eq_zero
    {J : Type*} [Category J]
    {G H : J ⥤ Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) (padicIntAbSheaf X l)}
    [HasLimit G] [HasLimit H] (φ : G ⟶ H) {a b : ℤ} (ha₀ : a ≠ 0) (hb₀ : b ≠ 0)
    (ha : ∀ j, a • kernel.ι (φ.app j) = 0) (hb : ∀ j, b • cokernel.π (φ.app j) = 0) :
    IsAdicLisseSheaf ((adicSheafExtendScalars X l).obj (limit G)) ↔
      IsAdicLisseSheaf ((adicSheafExtendScalars X l).obj (limit H)) :=
  have := isIso_adicSheafExtendScalars_map_limMap_of_zsmul_kernel_ι_app_eq_zero l φ ha₀ hb₀ ha hb
  ⟨IsAdicLisseSheaf.of_iso (asIso ((adicSheafExtendScalars X l).map (limMap φ))),
    IsAdicLisseSheaf.of_iso (asIso ((adicSheafExtendScalars X l).map (limMap φ))).symm⟩

/-- Powers of the prime `ℓ` are nonzero integers. -/
lemma natCast_prime_pow_ne_zero (a : ℕ) : ((l ^ a : ℕ) : ℤ) ≠ 0 :=
  Nat.cast_ne_zero.2 (pow_ne_zero _ (Fact.out : l.Prime).ne_zero)

variable (X) in
/-- **Rationalised limits of towers `ℓ`-adic up to bounded torsion are lisse** (target version).
Let `(Gₙ)` be an `ℓ`-adic tower of `ℤ_ℓ,X`-modules of rank `r` (transitions are cokernels of
`ℓⁿ` and `Gₙ` is locally `(ℤ/ℓⁿ)^r`), and let `φ : G ⟶ H` be a morphism of towers whose
components have kernels killed by `ℓ^a` and cokernels killed by `ℓ^b`. Then `ℚ̄_ℓ ⊗ lim Hₙ` is
lisse. -/
theorem isAdicLisseSheaf_adicSheafExtendScalars_limit_of_hom (r : ℕ)
    (G : ℕᵒᵖ ⥤ Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) (padicIntAbSheaf X l))
    (hG : ∀ n : ℕ, ∃ w : (((l ^ n : ℕ) : ℤ) • 𝟙 _) ≫
        (G ⋙ Mod.forget _).map (homOfLE n.le_succ).op = 0,
      Nonempty (IsColimit (CokernelCofork.ofπ _ w)))
    (hloc : ∀ (n : ℕ) (V : X.ProEt), ∃ S ∈ ProEt.topology X V,
      ∀ ⦃Y : X.ProEt⦄ (f : Y ⟶ V), S f →
        Nonempty ((isoPresheaf ((zmodPowAbSheafDiagramPow X l r).obj (op n))
          ((G ⋙ Mod.forget _).obj (op n))).obj (op Y)))
    (H : ℕᵒᵖ ⥤ Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) (padicIntAbSheaf X l))
    (φ : G ⟶ H) {a b : ℕ} (ha : ∀ n, ((l ^ a : ℕ) : ℤ) • kernel.ι (φ.app n) = 0)
    (hb : ∀ n, ((l ^ b : ℕ) : ℤ) • cokernel.π (φ.app n) = 0) :
    IsAdicLisseSheaf ((adicSheafExtendScalars X l).obj (limit H)) :=
  (isAdicLisseSheaf_adicSheafExtendScalars_limit_iff_of_zsmul_kernel_ι_app_eq_zero l φ
    (natCast_prime_pow_ne_zero l a) (natCast_prime_pow_ne_zero l b) ha hb).1
    (isAdicLisseSheaf_adicSheafExtendScalars_limit X l r G hG hloc)

variable (X) in
/-- **Rationalised limits of towers `ℓ`-adic up to bounded torsion are lisse** (source version).
Let `(Gₙ)` be an `ℓ`-adic tower of `ℤ_ℓ,X`-modules of rank `r` (transitions are cokernels of
`ℓⁿ` and `Gₙ` is locally `(ℤ/ℓⁿ)^r`), and let `φ : H ⟶ G` be a morphism of towers whose
components have kernels killed by `ℓ^a` and cokernels killed by `ℓ^b`. Then `ℚ̄_ℓ ⊗ lim Hₙ` is
lisse. -/
theorem isAdicLisseSheaf_adicSheafExtendScalars_limit_of_hom' (r : ℕ)
    (G : ℕᵒᵖ ⥤ Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) (padicIntAbSheaf X l))
    (hG : ∀ n : ℕ, ∃ w : (((l ^ n : ℕ) : ℤ) • 𝟙 _) ≫
        (G ⋙ Mod.forget _).map (homOfLE n.le_succ).op = 0,
      Nonempty (IsColimit (CokernelCofork.ofπ _ w)))
    (hloc : ∀ (n : ℕ) (V : X.ProEt), ∃ S ∈ ProEt.topology X V,
      ∀ ⦃Y : X.ProEt⦄ (f : Y ⟶ V), S f →
        Nonempty ((isoPresheaf ((zmodPowAbSheafDiagramPow X l r).obj (op n))
          ((G ⋙ Mod.forget _).obj (op n))).obj (op Y)))
    (H : ℕᵒᵖ ⥤ Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) (padicIntAbSheaf X l))
    (φ : H ⟶ G) {a b : ℕ} (ha : ∀ n, ((l ^ a : ℕ) : ℤ) • kernel.ι (φ.app n) = 0)
    (hb : ∀ n, ((l ^ b : ℕ) : ℤ) • cokernel.π (φ.app n) = 0) :
    IsAdicLisseSheaf ((adicSheafExtendScalars X l).obj (limit H)) :=
  (isAdicLisseSheaf_adicSheafExtendScalars_limit_iff_of_zsmul_kernel_ι_app_eq_zero l φ
    (natCast_prime_pow_ne_zero l a) (natCast_prime_pow_ne_zero l b) ha hb).2
    (isAdicLisseSheaf_adicSheafExtendScalars_limit X l r G hG hloc)

/-- **Lisseness of a rationalisation is local**: if `{gᵢ : Wᵢ ⟶ X}` is a pro-étale cover by
weakly étale morphisms and each `ℚ̄_ℓ ⊗ gᵢ^* M` is lisse, then `ℚ̄_ℓ ⊗ M` is lisse. -/
theorem isAdicLisseSheaf_adicSheafExtendScalars_of_cover {κ : Type*} {W : κ → Scheme.{u}}
    (g : ∀ i, W i ⟶ X) [∀ i, WeaklyEtale (g i)]
    (hg : Presieve.ofArrows W g ∈ Scheme.proetalePrecoverage X)
    (M : Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) (padicIntAbSheaf X l))
    (h : ∀ i, IsAdicLisseSheaf
      ((adicSheafExtendScalars (W i) l).obj ((padicIntModUpperStar l (g i)).obj M))) :
    IsAdicLisseSheaf ((adicSheafExtendScalars X l).obj M) :=
  IsAdicLisseSheaf.of_cover g hg fun i ↦
    (h i).of_iso ((padicIntModUpperStarCompAdicSheafExtendScalarsIso l (g i)).app M)

/-- The rationalisation `ℚ̄_ℓ ⊗ ℤ_ℓ,X^r` of a free `ℤ_ℓ,X`-module of finite rank is lisse. -/
lemma isAdicLisseSheaf_adicSheafExtendScalars_biproduct_regular (X : Scheme.{u}) (r : ℕ) :
    IsAdicLisseSheaf ((adicSheafExtendScalars X l).obj
      (⨁ fun _ : Fin r ↦ Mod.regular (padicIntAbSheaf X l))) :=
  ((isAdicLisseSheaf_adicConstantSheaf X).biproduct_const r).of_iso
    ((adicSheafExtendScalars X l).mapBiproduct _ ≪≫
      biproduct.mapIso fun _ ↦ adicSheafExtendScalarsRegularIso l X).symm

/-- **Local criterion for lisse rationalisations, via maps to free modules**: if `{gᵢ : Wᵢ ⟶ X}`
is a pro-étale cover by weakly étale morphisms and each `gᵢ^* M` admits a morphism to
`ℤ_ℓ,Wᵢ^{rᵢ}` with kernel and cokernel killed by nonzero integers, then `ℚ̄_ℓ ⊗ M` is lisse.
This applies to `M` pro-étale locally of the form `ℤ_ℓ^r ⊕ T` with `T` of bounded torsion. -/
theorem isAdicLisseSheaf_adicSheafExtendScalars_of_cover_of_hom {κ : Type*}
    {W : κ → Scheme.{u}} (g : ∀ i, W i ⟶ X) [∀ i, WeaklyEtale (g i)]
    (hg : Presieve.ofArrows W g ∈ Scheme.proetalePrecoverage X)
    (M : Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) (padicIntAbSheaf X l)) (r : κ → ℕ)
    (φ : ∀ i, (padicIntModUpperStar l (g i)).obj M ⟶
      ⨁ fun _ : Fin (r i) ↦ Mod.regular (padicIntAbSheaf (W i) l))
    {a b : κ → ℤ} (ha₀ : ∀ i, a i ≠ 0) (hb₀ : ∀ i, b i ≠ 0)
    (ha : ∀ i, a i • kernel.ι (φ i) = 0) (hb : ∀ i, b i • cokernel.π (φ i) = 0) :
    IsAdicLisseSheaf ((adicSheafExtendScalars X l).obj M) :=
  isAdicLisseSheaf_adicSheafExtendScalars_of_cover l g hg M fun i ↦
    (isAdicLisseSheaf_adicSheafExtendScalars_iff_of_zsmul_kernel_ι_eq_zero l (φ i) (ha₀ i)
      (hb₀ i) (ha i) (hb i)).2 (isAdicLisseSheaf_adicSheafExtendScalars_biproduct_regular l _ _)

/-- **Local criterion for lisse rationalisations, via maps from free modules**: if
`{gᵢ : Wᵢ ⟶ X}` is a pro-étale cover by weakly étale morphisms and each `gᵢ^* M` receives a
morphism from `ℤ_ℓ,Wᵢ^{rᵢ}` with kernel and cokernel killed by nonzero integers, then `ℚ̄_ℓ ⊗ M`
is lisse. -/
theorem isAdicLisseSheaf_adicSheafExtendScalars_of_cover_of_hom' {κ : Type*}
    {W : κ → Scheme.{u}} (g : ∀ i, W i ⟶ X) [∀ i, WeaklyEtale (g i)]
    (hg : Presieve.ofArrows W g ∈ Scheme.proetalePrecoverage X)
    (M : Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) (padicIntAbSheaf X l)) (r : κ → ℕ)
    (φ : ∀ i, (⨁ fun _ : Fin (r i) ↦ Mod.regular (padicIntAbSheaf (W i) l)) ⟶
      (padicIntModUpperStar l (g i)).obj M)
    {a b : κ → ℤ} (ha₀ : ∀ i, a i ≠ 0) (hb₀ : ∀ i, b i ≠ 0)
    (ha : ∀ i, a i • kernel.ι (φ i) = 0) (hb : ∀ i, b i • cokernel.π (φ i) = 0) :
    IsAdicLisseSheaf ((adicSheafExtendScalars X l).obj M) :=
  isAdicLisseSheaf_adicSheafExtendScalars_of_cover l g hg M fun i ↦
    (isAdicLisseSheaf_adicSheafExtendScalars_iff_of_zsmul_kernel_ι_eq_zero l (φ i) (ha₀ i)
      (hb₀ i) (ha i) (hb i)).1 (isAdicLisseSheaf_adicSheafExtendScalars_biproduct_regular l _ _)

/-- **Shifting a tower does not change its rationalised limit**: for `k : ℕ` and a tower `(Hₙ)`
of `ℤ_ℓ,X`-modules, `ℚ̄_ℓ ⊗ lim Hₙ₊ₖ` is lisse if and only if `ℚ̄_ℓ ⊗ lim Hₙ` is, the shift
`n ↦ n + k` being initial in `ℕᵒᵖ`. Combined with
`ProEtale.isAdicLisseSheaf_adicSheafExtendScalars_limit_iff_of_zsmul_kernel_ι_app_eq_zero`
this handles pro-morphisms of towers involving a shift of indices. -/
theorem isAdicLisseSheaf_adicSheafExtendScalars_limit_shift_iff (k : ℕ)
    (H : ℕᵒᵖ ⥤ Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) (padicIntAbSheaf X l)) :
    IsAdicLisseSheaf ((adicSheafExtendScalars X l).obj
        (limit ((Monotone.functor (f := fun n : ℕ ↦ n + k)
          fun _ _ h ↦ Nat.add_le_add_right h k).op ⋙ H))) ↔
      IsAdicLisseSheaf ((adicSheafExtendScalars X l).obj (limit H)) := by
  have hk : Monotone fun n : ℕ ↦ n + k := fun _ _ h ↦ Nat.add_le_add_right h k
  have : hk.functor.Final := (Monotone.final_functor_iff hk).2 fun j ↦ ⟨j, Nat.le_add_right j k⟩
  exact ⟨IsAdicLisseSheaf.of_iso ((adicSheafExtendScalars X l).mapIso
      (Functor.Initial.limitIso hk.functor.op H)),
    IsAdicLisseSheaf.of_iso ((adicSheafExtendScalars X l).mapIso
      (Functor.Initial.limitIso hk.functor.op H)).symm⟩

end AlgebraicGeometry.ProEtale
