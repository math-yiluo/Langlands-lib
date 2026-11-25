/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.Adic.TrivialDescent

/-!
# Morphisms of descents of free `ℓ`-adic sheaves

Let `f : W ⟶ X` be weakly étale, and `γ₁, γ₂` cocycles of sizes `n, m` on `W ×_X W`. A matrix
`A` of locally finite functions on `W` intertwining them, `γ₂ · p₁^* A = p₂^* A · γ₁`, induces a
morphism `descentSheaf f γ₁ ⟶ descentSheaf f γ₂` of their descents
(`AlgebraicGeometry.ProEtale.AdicSheaf.descentSheafMap`), functorially in `A`.

We also record that locally constant functions are locally finite
(`PadicAlgCl.lfOfLocallyConstant`) and that matrices of locally finite functions are determined
by their values (`PadicAlgCl.matrix_ext_locallyFiniteFunctionsEval`).
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite

attribute [local instance] Abelian.hasFiniteBiproducts

namespace PadicAlgCl

variable {l : ℕ} [Fact l.Prime] {T : Type*} [TopologicalSpace T]

/-- A locally constant function `T → ℚ̄_ℓ`, as a locally finite function: near every point it
takes a single value. -/
noncomputable def lfOfLocallyConstant (c : T → PadicAlgCl l) (hc : IsLocallyConstant c) :
    locallyFiniteFunctions l T :=
  ⟨⟨c, hc.continuous⟩, fun x ↦ ⟨c ⁻¹' {c x}, (hc.isOpen_fiber _).mem_nhds rfl,
    Submodule.finiteDimensional_of_le (S₂ := Submodule.span ℚ_[l] {c x})
      (Submodule.span_mono (by
        rintro _ ⟨y, hy, rfl⟩
        exact hy))⟩⟩

@[simp]
lemma lfOfLocallyConstant_apply (c : T → PadicAlgCl l) (hc : IsLocallyConstant c) (t : T) :
    (lfOfLocallyConstant c hc).1 t = c t :=
  rfl

/-- **Matrices of locally finite functions are determined by their values.** -/
lemma matrix_ext_locallyFiniteFunctionsEval {ι κ : Type*}
    {A B : Matrix ι κ (locallyFiniteFunctions l T)}
    (h : ∀ t, A.map (locallyFiniteFunctionsEval t) = B.map (locallyFiniteFunctionsEval t)) :
    A = B :=
  Matrix.ext fun i j ↦ Subtype.ext (ContinuousMap.ext fun t ↦ congrFun (congrFun (h t) i) j)

/-- A locally constant matrix-valued function, as a matrix of locally finite functions. -/
noncomputable def lfMatrixOfLocallyConstant {ι κ : Type*} (M : T → Matrix ι κ (PadicAlgCl l))
    (hM : IsLocallyConstant M) : Matrix ι κ (locallyFiniteFunctions l T) :=
  Matrix.of fun i j ↦ lfOfLocallyConstant (fun t ↦ M t i j)
    (hM.comp fun N : Matrix ι κ (PadicAlgCl l) ↦ N i j)

/-- The values of `PadicAlgCl.lfMatrixOfLocallyConstant`. -/
lemma lfMatrixOfLocallyConstant_map_eval {ι κ : Type*} (M : T → Matrix ι κ (PadicAlgCl l))
    (hM : IsLocallyConstant M) (t : T) :
    (lfMatrixOfLocallyConstant M hM).map (locallyFiniteFunctionsEval t) = M t :=
  Matrix.ext fun _ _ ↦ rfl

end PadicAlgCl

namespace AlgebraicGeometry.ProEtale.AdicSheaf

variable {l : ℕ} [Fact l.Prime]

section Pull

variable {W P : Scheme.{u}} (a : P ⟶ W) [WeaklyEtale a] {m n : ℕ}

/-- **Pulling back columns of functions is natural** in matrices of functions:
`p^* (A y) = (p^* A)(p^* y)`. -/
lemma ofUnitMatrix_comp_freePull
    (A : Matrix (Fin m) (Fin n) (PadicAlgCl.locallyFiniteFunctions l W)) :
    ofUnitMatrix A ≫ freePull a = freePull a ≫ (a)_*ᵃ[l].map
      (ofUnitMatrix (A.map (PadicAlgCl.locallyFiniteFunctionsComp l a.base.hom))) := by
  have h := unitMatrix_adicUpperStar (l := l) a (ofUnitMatrix A)
  rw [unitMatrix_ofUnitMatrix] at h
  rw [← h, ofUnitMatrix_unitMatrix, freePull, freePull, Category.assoc, ← Functor.map_comp,
    Iso.hom_inv_id_assoc, Functor.map_comp, ← Category.assoc, ← Category.assoc]
  congr 1
  exact (adicUpperStarLowerStarAdjunction l a).unit.naturality (ofUnitMatrix A)

end Pull

section DescentMap

variable {X W : Scheme.{u}} (f : W ⟶ X) [WeaklyEtale f] {m n : ℕ}
  (γ₁ : Matrix (Fin n) (Fin n) (PadicAlgCl.locallyFiniteFunctions l ↥(Limits.pullback f f)))
  (γ₂ : Matrix (Fin m) (Fin m) (PadicAlgCl.locallyFiniteFunctions l ↥(Limits.pullback f f)))
  (A : Matrix (Fin m) (Fin n) (PadicAlgCl.locallyFiniteFunctions l W))

/-- The first half of the descent map is natural in intertwining matrices. -/
lemma map_ofUnitMatrix_comp_descentMapFst
    (hA : γ₂ * A.map (PadicAlgCl.locallyFiniteFunctionsComp l (pullback.fst f f).base.hom) =
      A.map (PadicAlgCl.locallyFiniteFunctionsComp l (pullback.snd f f).base.hom) * γ₁) :
    (f)_*ᵃ[l].map (ofUnitMatrix A) ≫ descentMapFst f γ₂ =
      descentMapFst f γ₁ ≫ (pullback.fst f f ≫ f)_*ᵃ[l].map (ofUnitMatrix
        (A.map (PadicAlgCl.locallyFiniteFunctionsComp l (pullback.snd f f).base.hom))) := by
  rw [descentMapFst, descentMapFst, ← Category.assoc, ← Functor.map_comp, ← Category.assoc,
    ofUnitMatrix_comp_freePull, Category.assoc, ← Functor.map_comp, ← ofUnitMatrix_mul, hA,
    ofUnitMatrix_mul, Functor.map_comp, Functor.map_comp, Functor.map_comp, Functor.map_comp,
    Category.assoc, Category.assoc, Category.assoc, Category.assoc]
  congr 2
  exact (adicLowerStarComp l (pullback.fst f f) f).hom.naturality _

/-- The second half of the descent map is natural in matrices. -/
lemma map_ofUnitMatrix_comp_descentMapSnd :
    (f)_*ᵃ[l].map (ofUnitMatrix A) ≫ descentMapSnd (n := m) f =
      descentMapSnd (n := n) f ≫ (pullback.fst f f ≫ f)_*ᵃ[l].map (ofUnitMatrix
        (A.map (PadicAlgCl.locallyFiniteFunctionsComp l (pullback.snd f f).base.hom))) := by
  have h₁ := (adicLowerStarComp l (pullback.snd f f) f).hom.naturality (ofUnitMatrix
    (A.map (PadicAlgCl.locallyFiniteFunctionsComp l (pullback.snd f f).base.hom)))
  have h₂ := (adicLowerStarCongr l (pullback.condition (f := f) (g := f)).symm).hom.naturality
    (ofUnitMatrix (A.map (PadicAlgCl.locallyFiniteFunctionsComp l (pullback.snd f f).base.hom)))
  dsimp only [Functor.comp_map] at h₁
  rw [descentMapSnd, descentMapSnd, ← Functor.map_comp_assoc, ofUnitMatrix_comp_freePull,
    Functor.map_comp, Category.assoc, Category.assoc, Category.assoc, reassoc_of% h₁, h₂]

/-- **The descent map is natural in intertwining matrices**: if `γ₂ · p₁^* A = p₂^* A · γ₁`,
then `A` carries the kernel of the descent map of `γ₁` to that of `γ₂`. -/
lemma map_ofUnitMatrix_comp_descentMap
    (hA : γ₂ * A.map (PadicAlgCl.locallyFiniteFunctionsComp l (pullback.fst f f).base.hom) =
      A.map (PadicAlgCl.locallyFiniteFunctionsComp l (pullback.snd f f).base.hom) * γ₁) :
    (f)_*ᵃ[l].map (ofUnitMatrix A) ≫ descentMap f γ₂ =
      descentMap f γ₁ ≫ (pullback.fst f f ≫ f)_*ᵃ[l].map (ofUnitMatrix
        (A.map (PadicAlgCl.locallyFiniteFunctionsComp l (pullback.snd f f).base.hom))) := by
  rw [descentMap_eq, descentMap_eq, Preadditive.comp_sub, Preadditive.sub_comp,
    map_ofUnitMatrix_comp_descentMapFst f γ₁ γ₂ A hA, map_ofUnitMatrix_comp_descentMapSnd]

/-- **The morphism of descents induced by an intertwining matrix** `A`,
`γ₂ · p₁^* A = p₂^* A · γ₁`: multiplication by `A` on sections. -/
noncomputable def descentSheafMap
    (hA : γ₂ * A.map (PadicAlgCl.locallyFiniteFunctionsComp l (pullback.fst f f).base.hom) =
      A.map (PadicAlgCl.locallyFiniteFunctionsComp l (pullback.snd f f).base.hom) * γ₁) :
    descentSheaf f γ₁ ⟶ descentSheaf f γ₂ :=
  kernel.lift _ (kernel.ι (descentMap f γ₁) ≫ (f)_*ᵃ[l].map (ofUnitMatrix A)) (by
    rw [Category.assoc, map_ofUnitMatrix_comp_descentMap f γ₁ γ₂ A hA, kernel.condition_assoc,
      zero_comp])

/-- The morphism of descents induced by a matrix, followed by the inclusion. -/
lemma descentSheafMap_ι
    (hA : γ₂ * A.map (PadicAlgCl.locallyFiniteFunctionsComp l (pullback.fst f f).base.hom) =
      A.map (PadicAlgCl.locallyFiniteFunctionsComp l (pullback.snd f f).base.hom) * γ₁) :
    descentSheafMap f γ₁ γ₂ A hA ≫ kernel.ι (descentMap f γ₂) =
      kernel.ι (descentMap f γ₁) ≫ (f)_*ᵃ[l].map (ofUnitMatrix A) :=
  kernel.lift_ι _ _ _

/-- **Functoriality of the morphisms of descents**: if `B A = 1`, the composite of the morphisms
induced by `A` and `B` is the identity. -/
lemma descentSheafMap_comp_descentSheafMap {B : Matrix (Fin n) (Fin m)
      (PadicAlgCl.locallyFiniteFunctions l W)}
    (hA : γ₂ * A.map (PadicAlgCl.locallyFiniteFunctionsComp l (pullback.fst f f).base.hom) =
      A.map (PadicAlgCl.locallyFiniteFunctionsComp l (pullback.snd f f).base.hom) * γ₁)
    (hB : γ₁ * B.map (PadicAlgCl.locallyFiniteFunctionsComp l (pullback.fst f f).base.hom) =
      B.map (PadicAlgCl.locallyFiniteFunctionsComp l (pullback.snd f f).base.hom) * γ₂)
    (hBA : B * A = 1) :
    descentSheafMap f γ₁ γ₂ A hA ≫ descentSheafMap f γ₂ γ₁ B hB = 𝟙 _ := by
  rw [← cancel_mono (kernel.ι (descentMap f γ₁)), Category.assoc, descentSheafMap_ι,
    ← Category.assoc, descentSheafMap_ι, Category.assoc,
    ← Functor.map_comp, ← ofUnitMatrix_mul, hBA, ofUnitMatrix_one]
  simp

end DescentMap

end AlgebraicGeometry.ProEtale.AdicSheaf
