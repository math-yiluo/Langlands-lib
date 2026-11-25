/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.Adic.ZModPowGLLift

/-!
# Lattices of `ℓ`-adic towers of rank `r` are locally `ℤ_ℓ,X^r`

Finite direct sums commute with limits (`CategoryTheory.Limits.Cone.biproductPow` and
`CategoryTheory.Limits.IsLimit.biproductPow`), so the limit of the tower `(ℤ/ℓⁿ)_X^r` is the
direct sum `ℤ_ℓ,X^r` of `r` copies of `ℤ_ℓ,X`
(`AlgebraicGeometry.ProEtale.limitZmodPowAbSheafDiagramPowIso`). Hence an `ℓ`-adic tower `(Gₙ)` of
pro-étale abelian sheaves with each `Gₙ` locally isomorphic to `(ℤ/ℓⁿ)_X^r` has a limit `lim Gₙ`
which is pro-étale locally isomorphic to `ℤ_ℓ,X^r`
(`AlgebraicGeometry.ProEtale.exists_cover_nonempty_iso_padicIntAbSheaf_pow`).
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite

attribute [local instance] Abelian.hasFiniteBiproducts

namespace CategoryTheory.Limits

variable {K D : Type*} [Category* K] [Category* D] [Preadditive D] [HasFiniteBiproducts D]
  {F : K ⥤ D} (ι : Type*) [Finite ι]

/-- The direct sum of `ι` copies of a cone over `F`, as a cone over `F.biproductPow ι`. -/
@[simps]
noncomputable def Cone.biproductPow (c : Cone F) : Cone (F.biproductPow ι) where
  pt := ⨁ fun _ : ι ↦ c.pt
  π :=
    { app k := biproduct.map fun _ ↦ c.π.app k
      naturality k k' f := biproduct.hom_ext _ _ fun i ↦ by simp }

/-- **Finite direct sums commute with limits**: the direct sum of `ι` copies of a limit cone is
a limit cone. -/
noncomputable def IsLimit.biproductPow {c : Cone F} (hc : IsLimit c) :
    IsLimit (c.biproductPow ι) where
  lift s := biproduct.lift fun i ↦ hc.lift
    { pt := s.pt
      π :=
        { app k := s.π.app k ≫ biproduct.π _ i
          naturality k k' f := by simp [← s.w f] } }
  fac s k := by
    refine biproduct.hom_ext _ _ fun i ↦ ?_
    rw [Category.assoc, Cone.biproductPow_π_app, biproduct.map_π, biproduct.lift_π_assoc,
      hc.fac]
  uniq s m hm := by
    refine biproduct.hom_ext _ _ fun i ↦ ?_
    rw [biproduct.lift_π]
    refine hc.hom_ext fun k ↦ ?_
    rw [hc.fac]
    simp [← hm k]

end CategoryTheory.Limits

namespace AlgebraicGeometry.ProEtale

open Scheme

variable (X : Scheme.{u}) (l : ℕ) [Fact l.Prime]

/-- **`lim_n (ℤ/ℓⁿ)_X^r ≅ ℤ_ℓ,X^r`** as abelian sheaves on `X_proét`. -/
noncomputable def limitZmodPowAbSheafDiagramPowIso (r : ℕ) :
    limit (zmodPowAbSheafDiagramPow X l r) ≅ ⨁ fun _ : Fin r ↦ padicIntAbSheaf X l :=
  (limit.isLimit _).conePointUniqueUpToIso ((isLimitPadicIntAbSheafCone X l).biproductPow (Fin r))

/-- **An `ℓ`-adic tower of sheaves locally isomorphic to `(ℤ/ℓⁿ)_X^r` has a lattice which is
locally `ℤ_ℓ,X^r`.** Let `(Gₙ)` be a tower of pro-étale abelian sheaves whose transitions are,
locally, cokernels of `ℓⁿ` (i.e. `Gₙ₊₁/ℓⁿ ≅ Gₙ`), with each `Gₙ` locally isomorphic to
`(ℤ/ℓⁿ)_X^r`. Then `lim Gₙ` is isomorphic to `ℤ_ℓ,X^r` over the members of a pro-étale cover of
any object. -/
theorem exists_cover_nonempty_iso_padicIntAbSheaf_pow (r : ℕ)
    (G : ℕᵒᵖ ⥤ Sheaf (ProEt.topology X) Ab.{u + 1})
    (hG : ∀ (n : ℕ) (Y : X.ProEt), ∃ w : (((l ^ n : ℕ) : ℤ) • 𝟙 _) ≫
        ((ProEt.topology X).overPullback Ab.{u + 1} Y).map (G.map (homOfLE n.le_succ).op) = 0,
      Nonempty (IsColimit (CokernelCofork.ofπ _ w)))
    (hloc : ∀ (n : ℕ) (V : X.ProEt), ∃ S ∈ ProEt.topology X V,
      ∀ ⦃Y : X.ProEt⦄ (f : Y ⟶ V), S f →
        Nonempty ((isoPresheaf ((zmodPowAbSheafDiagramPow X l r).obj (op n))
          (G.obj (op n))).obj (op Y)))
    (V : X.ProEt) :
    ∃ (ι : Type u) (W : ι → X.ProEt) (f : ∀ i, W i ⟶ V),
      Sieve.ofArrows W f ∈ ProEt.topology X V ∧
      ∀ i, Nonempty (((ProEt.topology X).overPullback Ab.{u + 1} (W i)).obj (limit G) ≅
        ((ProEt.topology X).overPullback Ab.{u + 1} (W i)).obj
          (⨁ fun _ : Fin r ↦ padicIntAbSheaf X l)) := by
  obtain ⟨ι, W, f, hcov, h⟩ :=
    exists_cover_nonempty_iso_limit_zmodPowAbSheafDiagramPow X l r G hG hloc V
  exact ⟨ι, W, f, hcov, fun i ↦ ⟨(h i).some ≪≫
    ((ProEt.topology X).overPullback Ab.{u + 1} (W i)).mapIso
      (limitZmodPowAbSheafDiagramPowIso X l r)⟩⟩

variable {X} in
/-- Restriction of abelian sheaves on `X_proét` to a slice preserves colimits: it is left adjoint
to the pushforward along the cocontinuous functor `Over.forget Y`. -/
instance preservesColimitsOfSize_overPullback (Y : X.ProEt) :
    PreservesColimitsOfSize.{0, 0} ((ProEt.topology X).overPullback Ab.{u + 1} Y) :=
  ((Over.forget Y).sheafAdjunctionCocontinuous Ab.{u + 1} ((ProEt.topology X).over Y)
    (ProEt.topology X)).leftAdjoint_preservesColimits

variable {X} in
/-- A cokernel of multiplication by an integer `N` remains one after restriction to any slice:
restriction preserves colimits. -/
lemma exists_isColimit_cokernelCofork_overPullback {A B : Sheaf (ProEt.topology X) Ab.{u + 1}}
    {N : ℤ} {π : A ⟶ B} {w : (N • 𝟙 A) ≫ π = 0} (h : IsColimit (CokernelCofork.ofπ π w))
    (Y : X.ProEt) :
    ∃ w' : (N • 𝟙 _) ≫ ((ProEt.topology X).overPullback Ab.{u + 1} Y).map π = 0,
      Nonempty (IsColimit (CokernelCofork.ofπ _ w')) :=
  exists_isColimit_cokernelCofork_of_iso
    (w := by rw [← Functor.map_comp, Cofork.π_ofπ, w, Functor.map_zero])
    (CokernelCofork.mapIsColimit _ h ((ProEt.topology X).overPullback Ab.{u + 1} Y))
    (Iso.refl _) (Iso.refl _)
    (by
      rw [Iso.refl_hom, Category.comp_id, Category.id_comp, Functor.map_zsmul,
        CategoryTheory.Functor.map_id])
    (by
      rw [Iso.refl_hom, Iso.refl_hom, Category.comp_id, Category.id_comp]
      rfl)

/-- **An `ℓ`-adic tower of sheaves locally isomorphic to `(ℤ/ℓⁿ)_X^r` has a lattice which is
locally `ℤ_ℓ,X^r`**, for a tower `(Gₙ)` whose transitions are cokernels of `ℓⁿ`
(`Gₙ₊₁/ℓⁿ ≅ Gₙ`) on `X_proét`; see `exists_cover_nonempty_iso_padicIntAbSheaf_pow`. -/
theorem exists_cover_nonempty_iso_padicIntAbSheaf_pow_of_isColimit (r : ℕ)
    (G : ℕᵒᵖ ⥤ Sheaf (ProEt.topology X) Ab.{u + 1})
    (hG : ∀ n : ℕ, ∃ w : (((l ^ n : ℕ) : ℤ) • 𝟙 _) ≫ G.map (homOfLE n.le_succ).op = 0,
      Nonempty (IsColimit (CokernelCofork.ofπ _ w)))
    (hloc : ∀ (n : ℕ) (V : X.ProEt), ∃ S ∈ ProEt.topology X V,
      ∀ ⦃Y : X.ProEt⦄ (f : Y ⟶ V), S f →
        Nonempty ((isoPresheaf ((zmodPowAbSheafDiagramPow X l r).obj (op n))
          (G.obj (op n))).obj (op Y)))
    (V : X.ProEt) :
    ∃ (ι : Type u) (W : ι → X.ProEt) (f : ∀ i, W i ⟶ V),
      Sieve.ofArrows W f ∈ ProEt.topology X V ∧
      ∀ i, Nonempty (((ProEt.topology X).overPullback Ab.{u + 1} (W i)).obj (limit G) ≅
        ((ProEt.topology X).overPullback Ab.{u + 1} (W i)).obj
          (⨁ fun _ : Fin r ↦ padicIntAbSheaf X l)) :=
  exists_cover_nonempty_iso_padicIntAbSheaf_pow X l r G
    (fun n Y ↦ exists_isColimit_cokernelCofork_overPullback (hG n).choose_spec.some Y) hloc V

/-- **An `ℓ`-adic tower of sheaves locally isomorphic to `(ℤ/ℓⁿ)_X` has a lattice which is
locally `ℤ_ℓ,X`**, for a tower `(Gₙ)` whose transitions are cokernels of `ℓⁿ`
(`Gₙ₊₁/ℓⁿ ≅ Gₙ`) on `X_proét`; see `exists_cover_nonempty_iso_padicIntAbSheaf_of_locally_iso`. -/
theorem exists_cover_nonempty_iso_padicIntAbSheaf_of_isColimit
    (G : ℕᵒᵖ ⥤ Sheaf (ProEt.topology X) Ab.{u + 1})
    (hG : ∀ n : ℕ, ∃ w : (((l ^ n : ℕ) : ℤ) • 𝟙 _) ≫ G.map (homOfLE n.le_succ).op = 0,
      Nonempty (IsColimit (CokernelCofork.ofπ _ w)))
    (hloc : ∀ (n : ℕ) (V : X.ProEt), ∃ S ∈ ProEt.topology X V,
      ∀ ⦃Y : X.ProEt⦄ (f : Y ⟶ V), S f →
        Nonempty ((isoPresheaf ((zmodPowAbSheafDiagram X l).obj (op n)) (G.obj (op n))).obj
          (op Y)))
    (V : X.ProEt) :
    ∃ (ι : Type u) (W : ι → X.ProEt) (f : ∀ i, W i ⟶ V),
      Sieve.ofArrows W f ∈ ProEt.topology X V ∧
      ∀ i, Nonempty (((ProEt.topology X).overPullback Ab.{u + 1} (W i)).obj (limit G) ≅
        ((ProEt.topology X).overPullback Ab.{u + 1} (W i)).obj (padicIntAbSheaf X l)) :=
  exists_cover_nonempty_iso_padicIntAbSheaf_of_locally_iso X l G
    (fun n Y ↦ exists_isColimit_cokernelCofork_overPullback (hG n).choose_spec.some Y) hloc V

end AlgebraicGeometry.ProEtale
