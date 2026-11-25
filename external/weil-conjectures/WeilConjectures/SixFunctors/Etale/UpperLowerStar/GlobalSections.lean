/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Sites.GlobalSections
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.TopologicalInvariance

/-!
# Global sections of a pushforward and of a pullback of étale sheaves

For a morphism of schemes `f : X ⟶ Y`, this file identifies the global sections of a
pushforward, `Γ(Y, f_* F) ≅ Γ(X, F)`. For an étale sheaf `G` on `Y`, it constructs the pullback
map `Γ(Y, G) ⟶ Γ(X, f^* G)` on global sections, and shows that it is an isomorphism when `f` is.

## Main definitions

- `AlgebraicGeometry.Etale.lowerStarCompGlobalSectionsIso`: the isomorphism
  `f_* ⋙ Γ_Y ≅ Γ_X`.
- `AlgebraicGeometry.Etale.globalSectionsUpperStarMap`: the map `Γ(Y, G) ⟶ Γ(X, f^* G)`.
- `AlgebraicGeometry.Etale.globalSectionsUpperStarIso`: the isomorphism
  `Γ(Y, G) ≅ Γ(X, f^* G)` for an isomorphism `f`.
-/

@[expose] public section

universe u' u

open CategoryTheory Limits Opposite Abelian

namespace AlgebraicGeometry.Etale

open Scheme

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [HasSmallSiteSheafify A] {X Y : Scheme.{u}} (f : X ⟶ Y) (G : Sheaf Y.smallEtaleTopology A)

/-- Global sections are invariant under the pushforward along a morphism `f : X ⟶ Y`:
`Γ(Y, f_* F) ≅ (f_* F)(Y) = F(Y ×_Y X) ≅ F(X) ≅ Γ(X, F)`. -/
noncomputable def lowerStarCompGlobalSectionsIso :
    (f)_*[A] ⋙ Sheaf.Γ Y.smallEtaleTopology A ≅ Sheaf.Γ X.smallEtaleTopology A :=
  Functor.isoWhiskerLeft _ (Sheaf.ΓNatIsoSheafSections _ _ terminalIsTerminal) ≪≫
    lowerStarCompSheafSectionsTerminalIso A f ≪≫
    (Sheaf.ΓNatIsoSheafSections _ _ terminalIsTerminal).symm

/-- The pullback map on global sections

`Γ(Y, G) ≅ G(Y) ⟶ (f_* f^* G)(Y) = (f^* G)(Y ×_Y X) ≅ (f^* G)(X) ≅ Γ(X, f^* G)`,

given by the unit `G ⟶ f_* f^* G` of the adjunction `f^* ⊣ f_*` evaluated at the terminal
object `Y` of the small étale site of `Y`, and the identification of its base change
`Y ×_Y X` with the terminal object `X` of the small étale site of `X`. For a finite `f` this is
the pullback `f^♯ a` of a section along a finite morphism.
(blueprint: `theorem-comparison-over-henselian-pair-degree`) -/
noncomputable def globalSectionsUpperStarMap :
    (Sheaf.Γ _ A).obj G ⟶ (Sheaf.Γ _ A).obj ((f)^*[A].obj G) :=
  (Sheaf.ΓNatIsoSheafSections _ _ terminalIsTerminal).hom.app G ≫
    ((sheafSections _ _).obj (op (⊤_ _))).map ((upperStarLowerStarAdjunction A f).unit.app G) ≫
    ((f)^*[A].obj G).obj.map (PreservesTerminal.iso f.Etale).inv.op ≫
    (Sheaf.ΓNatIsoSheafSections _ _ terminalIsTerminal).inv.app _

/-- The pullback map on global sections along an isomorphism is an isomorphism: the pullback
along an isomorphism is an equivalence, so the unit of `f^* ⊣ f_*` is an isomorphism. -/
instance [IsIso f] : IsIso (globalSectionsUpperStarMap A f G) := by
  have := isEquivalence_upperStar A f
  unfold globalSectionsUpperStarMap
  infer_instance

/-- The isomorphism `Γ(Y, G) ≅ Γ(X, f^* G)` of global sections along an isomorphism
`f : X ⟶ Y`, see `AlgebraicGeometry.Etale.globalSectionsUpperStarMap`. -/
noncomputable def globalSectionsUpperStarIso [IsIso f] :
    (Sheaf.Γ _ A).obj G ≅ (Sheaf.Γ _ A).obj ((f)^*[A].obj G) :=
  asIso (globalSectionsUpperStarMap A f G)

/-- The structure morphism of the terminal object of the small étale site of `X` is an
isomorphism: the terminal object is isomorphic to `𝟙 X`. -/
lemma isIso_terminal_hom (X : Scheme.{u}) : IsIso (⊤_ X.Etale).hom := by
  let e := terminalIsTerminal.uniqueUpToIso
    (MorphismProperty.Over.mkIdTerminal @AlgebraicGeometry.Etale X)
  have : IsIso e.hom.left :=
    ⟨e.inv.left, congrArg (·.left) e.hom_inv_id, congrArg (·.left) e.inv_hom_id⟩
  have h : e.hom.left = (⊤_ X.Etale).hom :=
    (Category.comp_id _).symm.trans (MorphismProperty.Over.w e.hom)
  rw [← h]
  exact this

/-- In degree zero the comparison map `AlgebraicGeometry.Etale.cohomologyMap` on étale
cohomology is bijective if and only if the pullback map on global sections
`AlgebraicGeometry.Etale.globalSectionsUpperStarMap` is an isomorphism: under
`H⁰(Y, G) ≅ Hom(ℤ_Y, G)` and `ℤ_X ≅ f^* ℤ_Y`, the comparison map becomes postcomposition with
the unit `G ⟶ f_* f^* G` of `f^* ⊣ f_*` followed by bijections, and under
`Hom(ℤ_Y, -) ≅ Γ(Y, -)` this postcomposition is the unit on global sections. -/
lemma bijective_cohomologyMap_zero_iff {X Y : Scheme.{u}} (f : X ⟶ Y)
    (G : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}) :
    Function.Bijective (cohomologyMap f G 0) ↔
      IsIso (globalSectionsUpperStarMap AddCommGrpCat.{u + 1} f G) := by
  let adj := upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} f
  let η : G ⟶ (f)_*[AddCommGrpCat.{u + 1}].obj ((f)^*[AddCommGrpCat.{u + 1}].obj G) :=
    adj.unit.app G
  let ι := (upperStarConstantSheafIso AddCommGrpCat.{u + 1} f).app
    (AddCommGrpCat.of (ULift ℤ))
  let Ψ : Sheaf.H ((f)_*[AddCommGrpCat.{u + 1}].obj ((f)^*[AddCommGrpCat.{u + 1}].obj G)) 0 →
      Sheaf.H ((f)^*[AddCommGrpCat.{u + 1}].obj G) 0 :=
    fun y ↦ Ext.mk₀ (ι.inv ≫ (adj.homEquiv _ _).symm (Ext.addEquiv₀ y))
  have hι : Function.Bijective (fun g : _ ⟶ (f)^*[AddCommGrpCat.{u + 1}].obj G ↦ ι.inv ≫ g) :=
    ⟨fun a b h ↦ (cancel_epi ι.inv).1 h, fun g ↦ ⟨ι.hom ≫ g, by simp⟩⟩
  have hΨ : Function.Bijective Ψ :=
    (Ext.mk₀_bijective _ _).comp (hι.comp
      ((adj.homEquiv _ _).symm.bijective.comp Ext.addEquiv₀.bijective))
  let e := Sheaf.H.equiv₀ G (terminalIsTerminal (C := Y.Etale))
  let e' := Sheaf.H.equiv₀ ((f)_*[AddCommGrpCat.{u + 1}].obj
    ((f)^*[AddCommGrpCat.{u + 1}].obj G)) (terminalIsTerminal (C := Y.Etale))
  have hfac : (cohomologyMap f G 0 : _ → _) =
      Ψ ∘ e'.symm ∘ η.hom.app (op (⊤_ Y.Etale)) ∘ e := by
    funext x
    obtain ⟨a, rfl⟩ := (Ext.mk₀_bijective _ _).2 x
    have h₁ : e'.symm (η.hom.app (op (⊤_ Y.Etale)) (e (Ext.mk₀ a))) =
        Sheaf.H.map η 0 (Ext.mk₀ a) := by
      rw [show e (Ext.mk₀ a) = Sheaf.H.equiv₀ G terminalIsTerminal (Ext.mk₀ a) from rfl,
        Sheaf.H.equiv₀_naturality]
      exact e'.symm_apply_apply _
    simp only [Function.comp_apply, h₁, Ψ, cohomologyMap_apply,
      Ext.mapExactFunctor_mk₀, Ext.mk₀_comp_mk₀]
    congr 1
    rw [Sheaf.H.addEquiv₀_map, ← Ext.addEquiv₀_symm_apply, AddEquiv.apply_symm_apply]
    simp [ι, adj, η, Adjunction.homEquiv_counit]
  rw [hfac, Function.Bijective.of_comp_iff' hΨ, Function.Bijective.of_comp_iff' e'.symm.bijective,
    Function.Bijective.of_comp_iff _ e.bijective, globalSectionsUpperStarMap,
    isIso_comp_left_iff, isIso_comp_right_iff, ConcreteCategory.isIso_iff_bijective]
  rfl

end AlgebraicGeometry.Etale
