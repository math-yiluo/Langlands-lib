/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.Adic.LisseLatticeTensor
public import WeilConjectures.SixFunctors.ProEtale.Adic.ContinuousMapAdd
public import WeilConjectures.SixFunctors.ProEtale.Adic.ContinuousMapReduction

/-!
# Lattice sections from morphisms of abelian sheaves

Let `R ⊆ ℚ̄_ℓ` be a topological ring with values in a finite extension `E` of `ℚ_ℓ` (typically
`R = 𝒪_E`). This file provides the two pieces of the maps `ψ_U : C(U, M) → F(U)` of
`AlgebraicGeometry.ProEtale.IsAdicLisseSheaf.of_bijective_tensorSections` which come from
morphisms of abelian sheaves:

- `AlgebraicGeometry.ProEtale.continuousMapAbSheafToAdicConstantSheaf`: the morphism
  `C(-, R) ⟶ ℚ̄_ℓ,X` of abelian sheaves (`𝒪_{E,X} ⟶ ℚ̄_ℓ,X` for `R = 𝒪_E`), `g ↦ ι ∘ g`;
- `AlgebraicGeometry.ProEtale.AdicSheaf.sectionsOfHom`: the maps on sections
  `C(U, M) → F(U)` induced by a morphism `C(-, M) ⟶ F` of abelian sheaves to the abelian sheaf
  underlying a sheaf `F` of `ℚ̄_ℓ,X`-modules, natural in `U`
  (`AlgebraicGeometry.ProEtale.AdicSheaf.sectionsOfHom_comp`), as in the hypothesis `hψ`.
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry.ProEtale

open PadicAlgCl Scheme

variable {l : ℕ} [Fact l.Prime] (X : Scheme.{u})
  {R : Type} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R] (ι : R →+* PadicAlgCl l)
  (hι : Continuous ι) {E : IntermediateField ℚ_[l] (PadicAlgCl l)} [FiniteDimensional ℚ_[l] E]
  (hιE : ∀ x, ι x ∈ E)

/-- The morphism of abelian sheaves `C(-, R) ⟶ ℚ̄_ℓ,X`, `g ↦ ι ∘ g`, for a continuous
`ι : R → ℚ̄_ℓ` with values in a finite extension `E` of `ℚ_ℓ`: for `R = 𝒪_E` this is the inclusion
`𝒪_{E,X} ⟶ ℚ̄_ℓ,X`. -/
noncomputable def continuousMapAbSheafToAdicConstantSheaf :
    continuousMapAbSheaf X R ⟶ (sheafCompose (ProEt.topology X)
      (forget₂ (WeilCoefficients.{u} l) Ab.{u + 1})).obj (adicConstantSheaf l X) where
  hom :=
    { app _ := AddCommGrpCat.ofHom
        { toFun g := ULift.up (AdicSheaf.ringValuedFunction ι hι hιE (ULift.down g))
          map_zero' := ULift.ext (Subtype.ext (ContinuousMap.ext fun _ ↦ map_zero ι))
          map_add' _ _ := ULift.ext (Subtype.ext (ContinuousMap.ext fun _ ↦ map_add ι _ _)) }
      naturality _ _ _ := rfl }

@[simp]
lemma continuousMapAbSheafToAdicConstantSheaf_app (U : X.ProEt) (g : C(U.left, R)) :
    (continuousMapAbSheafToAdicConstantSheaf X ι hι hιE).hom.app (op U) (ULift.up g) =
      ULift.up (AdicSheaf.ringValuedFunction ι hι hιE g) :=
  rfl

namespace AdicSheaf

variable {X} {M : Type} [TopologicalSpace M] [AddCommGroup M] [IsTopologicalAddGroup M]
  (F : AdicSheaf l X)
  (θ : continuousMapAddSheaf X M ⟶
    (sheafCompose (ProEt.topology X) (forget₂ (WeilCoefficients.{u} l) Ab.{u + 1})).obj F.X)

/-- The maps on sections `C(U, M) → F(U)` induced by a morphism `C(-, M) ⟶ F` of abelian
sheaves to the abelian sheaf underlying a sheaf of `ℚ̄_ℓ,X`-modules. -/
noncomputable def sectionsOfHom (U : X.ProEt) : C(U.left, M) →+ F.X.obj.obj (op U) :=
  (θ.hom.app (op U)).hom.comp (AddEquiv.ulift.{u, u + 1} (α := C(U.left, M))).symm.toAddMonoidHom

lemma sectionsOfHom_apply (U : X.ProEt) (m : C(U.left, M)) :
    sectionsOfHom F θ U m = θ.hom.app (op U) (ULift.up m) :=
  rfl

/-- The maps `C(U, M) → F(U)` induced by a morphism of abelian sheaves are natural in `U`. -/
lemma sectionsOfHom_comp ⦃U V : X.ProEt⦄ (f : V ⟶ U) (m : C(U.left, M)) :
    sectionsOfHom F θ V (m.comp f.left.base.hom) = F.X.obj.map f.op (sectionsOfHom F θ U m) :=
  ConcreteCategory.congr_hom (θ.hom.naturality f.op) (ULift.up m)

end AdicSheaf

end AlgebraicGeometry.ProEtale
