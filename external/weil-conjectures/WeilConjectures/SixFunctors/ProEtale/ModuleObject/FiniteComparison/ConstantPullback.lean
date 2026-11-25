/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Monoidal.Conjugate
public import WeilConjectures.CategoryTheory.Sites.ConstantSheafMonoidal
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.SectionsMonoidal
public import WeilConjectures.Mathlib.CategoryTheory.Sites.Monoidal
public import WeilConjectures.CategoryTheory.RingObjects.Ab
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.Defs

/-!
# The pullback of a constant sheaf is constant, monoidally

Let `F : C ⥤ D` be a continuous functor of essentially small sites sending a terminal object
`T₀` of `C` to a terminal object of `D` (isomorphic to a chosen terminal object `T₁`), and let
`L : Sheaf J Ab ⥤ Sheaf K Ab` be a strong monoidal left adjoint of the pushforward `F_*`, the
adjunction being monoidal; for instance the pullback `F^*` of sheaves along a representably flat
functor. Then `L` sends constant sheaves to constant sheaves, compatibly with the monoidal
structures: there is a monoidal natural isomorphism
```
c_D ≅ c_C ⋙ L
```
between the constant sheaf functors `c : Ab ⥤ Sheaf _ Ab`
(`CategoryTheory.constantSheafToPullback`). In particular `L` sends the constant ring sheaf
`T_C` to the constant ring sheaf `T_D`, as ring objects.

The comparison is the conjugate, for the adjunctions `c_C ⋙ L ⊣ F_* ⋙ Γ(T₀, -)` and
`c_D ⊣ Γ(T₁, -)`, of the identification `Γ(T₀, F_* G) = G(F T₀) ≅ G(T₁)`
(`CategoryTheory.pushforwardSectionsIso`). The latter is monoidal for the lax structures of
the sections functors induced by the underlying presheaf functors, since the lax structure of
`F_*` is the restriction along `F` on underlying presheaves
(`Functor.sheafPullbackConstruction.sheafToPresheafCompWhiskeringLeftIsoPushforward`), and the
constant sheaf adjunctions are monoidal (`CategoryTheory.isMonoidal_constantPresheafAdj`), so
the conjugate is monoidal by `CategoryTheory.isMonoidal_conjugateEquiv_symm`.
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory MonObj Limits Opposite Functor.LaxMonoidal
  Functor.OplaxMonoidal

namespace CategoryTheory

section ConstantPresheaf

variable {C : Type*} [Category* C] (A : Type*) [Category* A] [MonoidalCategory A] {T : C}
  (hT : IsTerminal T)

/-- The adjunction between the constant presheaf functor and the evaluation at a terminal
object is monoidal. -/
instance isMonoidal_constantPresheafAdj : (constantPresheafAdj A hT).IsMonoidal where
  leftAdjoint_ε := by
    simp [constantPresheafAdj]
    rfl
  leftAdjoint_μ X Y := by
    simp only [constantPresheafAdj]
    simp
    rfl

end ConstantPresheaf

section ConstantSheaf

variable {C : Type (u + 1)} [Category.{u} C] [EssentiallySmall.{u + 1} C]
  (J : GrothendieckTopology C) {T : C} (hT : IsTerminal T)

/-- The adjunction between the constant sheaf functor and the sections over a terminal object,
the right adjoint being written as the underlying presheaf followed by evaluation, so that it
carries the lax monoidal structure of this composite. -/
noncomputable def constantSheafSectionsAdj :
    constantSheaf J Ab.{u + 1} ⊣
      sheafToPresheaf J Ab.{u + 1} ⋙ (evaluation Cᵒᵖ Ab.{u + 1}).obj (op T) :=
  (constantPresheafAdj Ab.{u + 1} hT).comp (sheafificationAdjunction J Ab.{u + 1})

instance isMonoidal_constantSheafSectionsAdj : (constantSheafSectionsAdj J hT).IsMonoidal :=
  inferInstanceAs ((constantPresheafAdj Ab.{u + 1} hT).comp
    (sheafificationAdjunction J Ab.{u + 1})).IsMonoidal

end ConstantSheaf

section Pullback

variable {C D : Type (u + 1)} [Category.{u} C] [Category.{u} D] [EssentiallySmall.{u + 1} C]
  [EssentiallySmall.{u + 1} D] (J : GrothendieckTopology C) (K : GrothendieckTopology D)
  (F : C ⥤ D) [F.IsContinuous J K] {T₀ : C} {T₁ : D} (hT₁ : IsTerminal T₁)
  (hF : IsTerminal (F.obj T₀))

/-- Evaluating the restriction along `F.op` of a presheaf at `T₀` is evaluating it at `T₁`,
when `F.obj T₀` and `T₁` are both terminal. -/
noncomputable def whiskeringLeftEvaluationIso :
    (Functor.whiskeringLeft Cᵒᵖ Dᵒᵖ Ab.{u + 1}).obj F.op ⋙
        (evaluation Cᵒᵖ Ab.{u + 1}).obj (op T₀) ≅
      (evaluation Dᵒᵖ Ab.{u + 1}).obj (op T₁) :=
  NatIso.ofComponents (fun P ↦ P.mapIso (hT₁.uniqueUpToIso hF).op)
    fun f ↦ (f.naturality _).symm

instance : NatTrans.IsMonoidal (whiskeringLeftEvaluationIso F hT₁ hF).hom where
  unit := by
    simp [whiskeringLeftEvaluationIso]
  tensor P Q := by
    simp [whiskeringLeftEvaluationIso]

/-- The sections over `T₀` of the pushforward `F_* G` are the sections of `G` over `T₁`, when
`F.obj T₀` and `T₁` are both terminal. -/
noncomputable def pushforwardSectionsIso :
    F.sheafPushforwardContinuous Ab.{u + 1} J K ⋙
        (sheafToPresheaf J Ab.{u + 1} ⋙ (evaluation Cᵒᵖ Ab.{u + 1}).obj (op T₀)) ≅
      sheafToPresheaf K Ab.{u + 1} ⋙ (evaluation Dᵒᵖ Ab.{u + 1}).obj (op T₁) :=
  (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight
      (Functor.sheafPullbackConstruction.sheafToPresheafCompWhiskeringLeftIsoPushforward
        F Ab.{u + 1} J K).symm _ ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (whiskeringLeftEvaluationIso F hT₁ hF)

instance : NatTrans.IsMonoidal (pushforwardSectionsIso J K F hT₁ hF).hom := by
  dsimp only [pushforwardSectionsIso, Iso.trans_hom, Iso.symm_hom, Functor.isoWhiskerRight_hom,
    Functor.isoWhiskerLeft_hom]
  infer_instance

variable {J K F} {L : Sheaf J Ab.{u + 1} ⥤ Sheaf K Ab.{u + 1}} [L.Monoidal]
  (adj : L ⊣ F.sheafPushforwardContinuous Ab.{u + 1} J K) [adj.IsMonoidal] (hT₀ : IsTerminal T₀)

/-- The pullback of a constant sheaf is constant: the comparison `c_D ⟶ c_C ⋙ L` from the
constant sheaf functor on `D` to the pullback `L` of the constant sheaf functor on `C`, for a
continuous functor `F : C ⥤ D` preserving the terminal object. It is the conjugate of the
identification of the sections over the terminal objects `Γ(T₀, F_* -) ≅ Γ(T₁, -)`. -/
noncomputable def constantSheafToPullback :
    constantSheaf K Ab.{u + 1} ⟶ constantSheaf J Ab.{u + 1} ⋙ L :=
  (conjugateEquiv ((constantSheafSectionsAdj J hT₀).comp adj)
    (constantSheafSectionsAdj K hT₁)).symm (pushforwardSectionsIso J K F hT₁ hF).hom

instance : IsIso (constantSheafToPullback hT₁ hF adj hT₀) := by
  dsimp only [constantSheafToPullback]
  infer_instance

instance : NatTrans.IsMonoidal (constantSheafToPullback hT₁ hF adj hT₀) :=
  isMonoidal_conjugateEquiv_symm _ _ _

end Pullback

end CategoryTheory
