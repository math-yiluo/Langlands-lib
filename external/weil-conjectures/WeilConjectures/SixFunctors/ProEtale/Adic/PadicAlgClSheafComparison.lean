/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.RingObjects.EllAdic
public import WeilConjectures.SixFunctors.ProEtale.Adic.ConstantSheaf

/-!
# Comparison of the two constructions of `ℚ̄_ℓ,X`

The repository has two models of the constant `ℓ`-adic sheaf `ℚ̄_ℓ,X` on `X_proét`:

* `AlgebraicGeometry.ProEtale.padicAlgClSheaf X ℓ`, the abelian sheaf (ring object) obtained by
  sheafifying the presheaf of continuous functions `U → ℚ̄_ℓ` with values in a finite
  subextension `E ⊆ ℚ̄_ℓ` (`PadicAlgCl.finiteIntermediateFieldValued`);
* `AlgebraicGeometry.ProEtale.adicConstantSheaf ℓ X`, the sheaf of `ℚ̄_ℓ`-modules of continuous
  functions whose values locally span finite-dimensional `ℚ_ℓ`-subspaces
  (`PadicAlgCl.locallyFiniteFunctions`), the unit of the `ℓ`-adic sheaves `AdicSheaf`.

A function with values in a finite subextension is locally finite
(`PadicAlgCl.finiteIntermediateFieldValued_le_locallyFiniteFunctions`), so the defining
presheaf of the first maps to the second, and by the universal property of sheafification this
induces a morphism of abelian sheaves `padicAlgClSheaf X ℓ ⟶ adicConstantSheaf ℓ X`
(`AlgebraicGeometry.ProEtale.padicAlgClSheafToAdicConstantSheaf`).

## Main definitions

- `AlgebraicGeometry.ProEtale.padicAlgClPresheafToAdicConstantSheaf`: the inclusion on the
  defining presheaves.
- `AlgebraicGeometry.ProEtale.padicAlgClSheafToAdicConstantSheaf`: the induced morphism of
  abelian sheaves.
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite

namespace PadicAlgCl

variable (l : ℕ) [Fact l.Prime] (T : Type*) [TopologicalSpace T]

/-- A continuous function with values in a finite subextension `E ⊆ ℚ̄_ℓ` of `ℚ_ℓ` is locally
finite: all its values lie in the finite-dimensional `ℚ_ℓ`-subspace `E`. -/
lemma finiteIntermediateFieldValued_le_locallyFiniteFunctions :
    finiteIntermediateFieldValued l T ≤ (locallyFiniteFunctions l T).toSubring := by
  rintro f ⟨E, hE, hf⟩ x
  refine ⟨Set.univ, Filter.univ_mem, Submodule.finiteDimensional_of_le
    (S₂ := Subalgebra.toSubmodule E.toSubalgebra) (Submodule.span_le.2 ?_)⟩
  rintro _ ⟨y, -, rfl⟩
  exact hf y

end PadicAlgCl

namespace AlgebraicGeometry.ProEtale

open Scheme

variable (X : Scheme.{u}) (l : ℕ) [Fact l.Prime]

/-- The inclusion of the presheaf of functions with values in a finite subextension into the
locally finite functions, as a morphism of presheaves of abelian groups on `X_proét` from the
presheaf whose sheafification is `padicAlgClSheaf X ℓ` to the abelian sheaf underlying
`adicConstantSheaf ℓ X`. -/
noncomputable def padicAlgClPresheafToAdicConstantSheaf :
    padicAlgClRingPresheaf X l ⋙ forget₂ RingCat.{u + 1} Ab.{u + 1} ⟶
      ((sheafCompose (ProEt.topology X) (forget₂ (WeilCoefficients.{u} l) Ab.{u + 1})).obj
        (adicConstantSheaf l X)).obj where
  app _ := AddCommGrpCat.ofHom
    { toFun x := ULift.up ⟨x.down.1,
        PadicAlgCl.finiteIntermediateFieldValued_le_locallyFiniteFunctions l _ x.down.2⟩
      map_zero' := rfl
      map_add' _ _ := rfl }
  naturality _ _ _ := rfl

/-- **Comparison of the two models of `ℚ̄_ℓ,X`**: the morphism of abelian sheaves
`padicAlgClSheaf X ℓ ⟶ adicConstantSheaf ℓ X` induced, by the universal property of
sheafification, by the inclusion of the functions with values in a finite subextension into the
locally finite functions. -/
noncomputable def padicAlgClSheafToAdicConstantSheaf :
    padicAlgClSheaf X l ⟶
      (sheafCompose (ProEt.topology X) (forget₂ (WeilCoefficients.{u} l) Ab.{u + 1})).obj
        (adicConstantSheaf l X) :=
  ((sheafificationAdjunction (ProEt.topology X) Ab.{u + 1}).homEquiv _ _).symm
    (padicAlgClPresheafToAdicConstantSheaf X l)

/-- The inclusion of the presheaf of functions with values in a finite subextension into the
locally finite functions is a monomorphism of presheaves. -/
instance mono_padicAlgClPresheafToAdicConstantSheaf :
    Mono (padicAlgClPresheafToAdicConstantSheaf X l) := by
  have (U : X.ProEtᵒᵖ) : Mono ((padicAlgClPresheafToAdicConstantSheaf X l).app U) :=
    (AddCommGrpCat.mono_iff_injective _).2 fun x y h ↦
      ULift.ext (Subtype.ext (congrArg (fun z ↦ z.down.1) h))
  exact NatTrans.mono_of_mono_app _

/-- `padicAlgClSheaf X ℓ ⟶ adicConstantSheaf ℓ X` is a monomorphism: sheafification preserves
monomorphisms. -/
instance mono_padicAlgClSheafToAdicConstantSheaf :
    Mono (padicAlgClSheafToAdicConstantSheaf X l) := by
  rw [padicAlgClSheafToAdicConstantSheaf, Adjunction.homEquiv_counit]
  infer_instance

end AlgebraicGeometry.ProEtale
