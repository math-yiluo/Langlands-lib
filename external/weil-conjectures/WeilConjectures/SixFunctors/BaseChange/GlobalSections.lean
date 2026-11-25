/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.BaseChange.Square
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Coherence
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.GlobalSections

/-!
# Functoriality of the pullback of global sections

For a morphism of schemes `h : V ⟶ Y` and an étale sheaf `G` on `Y`, the pullback of global
sections `h^♯ : Γ(Y, G) ⟶ Γ(V, h^* G)` is `AlgebraicGeometry.Etale.globalSectionsUpperStarMap`,
given by the unit of `h^* ⊣ h_*`. It is functorial:

* along the identity it is the identity isomorphism `(𝟙 Y)^* G ≅ G`;
* along a composite `v ≫ u` it is the composite of the pullbacks, modulo
  `(v ≫ u)^* ≅ v^* u^*`;
* for a commutative square `a ≫ u = b ≫ i` the two composite pullbacks agree modulo the
  square isomorphism `b^* i^* ≅ a^* u^*`. Applied to the base change of a closed immersion
  `i : Z ⟶ T` along a finite `u : T' ⟶ T`, this says that pulling back a section to `T'` and
  restricting to the closed fibre `Z' = Z ×_T T'` is the same as restricting it to `Z` and
  pulling back to `Z'`.

These are the finite-pullback identities used in the degree-zero comparison over a
henselian pair; there the morphisms are finite, but finiteness plays no role here.

## Main statements

- `AlgebraicGeometry.Etale.globalSectionsUpperStarMap_id`
- `AlgebraicGeometry.Etale.globalSectionsUpperStarMap_comp`
- `AlgebraicGeometry.Etale.globalSectionsUpperStarMap_comp_squareUpperStarIso`
- `AlgebraicGeometry.Etale.globalSectionsUpperStarMap_descent`
- `AlgebraicGeometry.Etale.globalSectionsUpperStarMap_identities`
-/

@[expose] public section

universe u' u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry.Etale

open Scheme

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [HasSmallSiteSheafify A]

/-- **Finite pullback along the identity**: pulling back a section along `𝟙 Y` gives back the
section, under the identity isomorphism `(𝟙 Y)^* G ≅ G`: the triangle
```
Γ(Y, G) --(𝟙 Y)^♯--> Γ(Y, (𝟙 Y)^* G)
      \                   |
       𝟙                  | ≅
        \                 v
         `---------> Γ(Y, G)
```
commutes.
(blueprint: `theorem-comparison-over-henselian-pair-degree`) -/
@[reassoc]
lemma globalSectionsUpperStarMap_id {Y : Scheme.{u}} (G : Sheaf Y.smallEtaleTopology A) :
    globalSectionsUpperStarMap A (𝟙 Y) G ≫
      (Sheaf.Γ _ A).map ((upperStarId A Y).hom.app G) = 𝟙 _ := by
  have hη := congr_arg (fun f ↦ f.hom.app (op (⊤_ Y.Etale)))
    (upperStarId_hom_app_unit_app A Y G)
  simp only [ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app, lowerStarId,
    GrothendieckTopology.lowerStarId, Functor.sheafPushforwardContinuousId'_inv_app_hom_app] at hη
  have key : ((upperStarLowerStarAdjunction A (𝟙 Y)).unit.app G).hom.app (op (⊤_ Y.Etale)) ≫
      ((𝟙 Y)^*[A].obj G).obj.map (PreservesTerminal.iso (Hom.Etale (𝟙 Y))).inv.op ≫
        ((upperStarId A Y).hom.app G).hom.app (op (⊤_ Y.Etale)) = 𝟙 _ := by
    erw [((upperStarId A Y).hom.app G).hom.naturality, reassoc_of% hη, ← Functor.map_comp]
    rw [← op_comp, terminal.hom_ext (_ ≫ _) (𝟙 _)]
    exact G.obj.map_id _
  simp only [globalSectionsUpperStarMap, Category.assoc]
  rw [← NatTrans.naturality]
  erw [reassoc_of% key]
  exact Iso.hom_inv_id_app _ _

/-- **Finite pullback along a composite**: for `v : T'' ⟶ T'` and `u : T' ⟶ T`, pulling a
section back along `v ≫ u` is pulling it back along `u` and then along `v`, under the
composition isomorphism `(v ≫ u)^* G ≅ v^* u^* G`: the square
```
Γ(T, G) ------(v ≫ u)^♯------> Γ(T'', (v ≫ u)^* G)
   |                                  |
  u^♯                                 | ≅
   v                                  v
Γ(T', u^* G) -------v^♯------> Γ(T'', v^* u^* G)
```
commutes.
(blueprint: `theorem-comparison-over-henselian-pair-degree`) -/
@[reassoc]
lemma globalSectionsUpperStarMap_comp {T'' T' T : Scheme.{u}} (v : T'' ⟶ T') (u : T' ⟶ T)
    (G : Sheaf T.smallEtaleTopology A) :
    globalSectionsUpperStarMap A (v ≫ u) G ≫
        (Sheaf.Γ _ A).map ((upperStarComp A v u).hom.app G) =
      globalSectionsUpperStarMap A u G ≫ globalSectionsUpperStarMap A v ((u)^*[A].obj G) := by
  have hη := congr_arg (fun f ↦ f.hom.app (op (⊤_ T.Etale)))
    (upperStarComp_hom_app_unit_app A v u G)
  simp only [ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app,
    Adjunction.comp_unit_app, lowerStarComp,
    Functor.sheafPushforwardContinuousComp'_hom_app_hom_app] at hη
  have key : ((upperStarLowerStarAdjunction A (v ≫ u)).unit.app G).hom.app (op (⊤_ T.Etale)) ≫
      ((v ≫ u)^*[A].obj G).obj.map (PreservesTerminal.iso (Hom.Etale (v ≫ u))).inv.op ≫
        ((upperStarComp A v u).hom.app G).hom.app (op (⊤_ T''.Etale)) =
      ((upperStarLowerStarAdjunction A u).unit.app G).hom.app (op (⊤_ T.Etale)) ≫
        ((u)^*[A].obj G).obj.map (PreservesTerminal.iso (Hom.Etale u)).inv.op ≫
        ((upperStarLowerStarAdjunction A v).unit.app ((u)^*[A].obj G)).hom.app
          (op (⊤_ T'.Etale)) ≫
        ((v)^*[A].obj ((u)^*[A].obj G)).obj.map (PreservesTerminal.iso (Hom.Etale v)).inv.op := by
    erw [((upperStarComp A v u).hom.app G).hom.naturality, reassoc_of% hη,
      ((upperStarLowerStarAdjunction A v).unit.app ((u)^*[A].obj G)).hom.naturality_assoc]
    congr 1
    refine congrArg₂ (· ≫ ·) rfl ?_
    erw [lowerStar_obj_val_map, ← Functor.map_comp, ← Functor.map_comp]
    congr 1
    rw [← op_comp, ← op_comp]
    exact congrArg Quiver.Hom.op
      (((terminalIsTerminal.isTerminalObj (Hom.Etale u)).isTerminalObj (Hom.Etale v)).hom_ext _ _)
  simp only [globalSectionsUpperStarMap, Category.assoc, Iso.inv_hom_id_app_assoc]
  rw [← NatTrans.naturality]
  congr 1
  exact (reassoc_of% key) _

/-- `AlgebraicGeometry.Etale.globalSectionsUpperStarMap_comp` for the composition isomorphism
`AlgebraicGeometry.Etale.upperStarComp` along a morphism `h₁₂` merely equal to `v ≫ u`. -/
@[reassoc]
lemma globalSectionsUpperStarMap_comp' {T'' T' T : Scheme.{u}} (v : T'' ⟶ T') (u : T' ⟶ T)
    (h₁₂ : T'' ⟶ T) (hh₁₂ : h₁₂ = v ≫ u) (G : Sheaf T.smallEtaleTopology A) :
    globalSectionsUpperStarMap A h₁₂ G ≫
        (Sheaf.Γ _ A).map ((upperStarComp A v u h₁₂ hh₁₂).hom.app G) =
      globalSectionsUpperStarMap A u G ≫ globalSectionsUpperStarMap A v ((u)^*[A].obj G) := by
  subst hh₁₂
  exact globalSectionsUpperStarMap_comp A v u G

/-- **Finite pullback and restriction to the closed fibre**: for a commutative square
```
Z' --a--> T'
|         |
b         u
v         v
Z  --i--> T
```
pulling a section back along `u` and then along `a` agrees with restricting it along `i` and
then pulling back along `b`, under the square isomorphism `b^* i^* G ≅ a^* u^* G`. It follows
from `AlgebraicGeometry.Etale.globalSectionsUpperStarMap_comp` applied to the two equal
composites `a ≫ u = b ≫ i`.
(blueprint: `theorem-comparison-over-henselian-pair-degree`) -/
@[reassoc]
lemma globalSectionsUpperStarMap_comp_squareUpperStarIso {Z' T' Z T : Scheme.{u}}
    {a : Z' ⟶ T'} {b : Z' ⟶ Z} {u : T' ⟶ T} {i : Z ⟶ T} (sq : CommSq a b u i)
    (G : Sheaf T.smallEtaleTopology A) :
    globalSectionsUpperStarMap A i G ≫ globalSectionsUpperStarMap A b ((i)^*[A].obj G) ≫
        (Sheaf.Γ _ A).map ((squareUpperStarIso A sq).hom.app G) =
      globalSectionsUpperStarMap A u G ≫ globalSectionsUpperStarMap A a ((u)^*[A].obj G) := by
  rw [← globalSectionsUpperStarMap_comp'_assoc A b i (a ≫ u) sq.w, ← Functor.map_comp,
    ← globalSectionsUpperStarMap_comp, squareUpperStarIso, Iso.trans_hom, Iso.symm_hom,
    NatTrans.comp_app, Iso.hom_inv_id_app_assoc]

/-- **Finite descent compatibility**: let `u : T' ⟶ T`, and let `x'` be a section of `u^* G`
over `T'` descended from a section `x` of `G` over `T`, that is `u^♯ x = x'`. Then the same
equality holds after restriction to a closed fibre: for a commutative square `a ≫ u = b ≫ i`,
the pullback `a^♯ x'` is the pullback along `b` of the restriction `i^♯ x`, under the square
isomorphism. Sections are taken with values in an arbitrary object `M`.
(blueprint: `theorem-comparison-over-henselian-pair-degree`) -/
lemma globalSectionsUpperStarMap_descent {Z' T' Z T : Scheme.{u}}
    {a : Z' ⟶ T'} {b : Z' ⟶ Z} {u : T' ⟶ T} {i : Z ⟶ T} (sq : CommSq a b u i)
    (G : Sheaf T.smallEtaleTopology A) {M : A} (x : M ⟶ (Sheaf.Γ _ A).obj G)
    (x' : M ⟶ (Sheaf.Γ _ A).obj ((u)^*[A].obj G)) (hx : x ≫ globalSectionsUpperStarMap A u G = x') :
    x' ≫ globalSectionsUpperStarMap A a ((u)^*[A].obj G) =
      x ≫ globalSectionsUpperStarMap A i G ≫ globalSectionsUpperStarMap A b ((i)^*[A].obj G) ≫
        (Sheaf.Γ _ A).map ((squareUpperStarIso A sq).hom.app G) := by
  rw [globalSectionsUpperStarMap_comp_squareUpperStarIso, ← hx, Category.assoc]

/-- **The finite-pullback identities**: the pullback of sections is the identity along the
identity, is compatible with composition, is compatible with restriction to closed fibres,
and preserves descended sections.
(blueprint: `theorem-comparison-over-henselian-pair-degree`) -/
theorem globalSectionsUpperStarMap_identities {Z' T' Z T : Scheme.{u}}
    {a : Z' ⟶ T'} {b : Z' ⟶ Z} {u : T' ⟶ T} {i : Z ⟶ T} (sq : CommSq a b u i)
    (G : Sheaf T.smallEtaleTopology A) :
    globalSectionsUpperStarMap A (𝟙 T) G ≫ (Sheaf.Γ _ A).map ((upperStarId A T).hom.app G) =
        𝟙 _ ∧
      globalSectionsUpperStarMap A (a ≫ u) G ≫
          (Sheaf.Γ _ A).map ((upperStarComp A a u).hom.app G) =
        globalSectionsUpperStarMap A u G ≫ globalSectionsUpperStarMap A a ((u)^*[A].obj G) ∧
      globalSectionsUpperStarMap A i G ≫ globalSectionsUpperStarMap A b ((i)^*[A].obj G) ≫
          (Sheaf.Γ _ A).map ((squareUpperStarIso A sq).hom.app G) =
        globalSectionsUpperStarMap A u G ≫ globalSectionsUpperStarMap A a ((u)^*[A].obj G) ∧
      ∀ {M : A} (x : M ⟶ (Sheaf.Γ _ A).obj G) (x' : M ⟶ (Sheaf.Γ _ A).obj ((u)^*[A].obj G)),
        x ≫ globalSectionsUpperStarMap A u G = x' →
          x' ≫ globalSectionsUpperStarMap A a ((u)^*[A].obj G) =
            x ≫ globalSectionsUpperStarMap A i G ≫
              globalSectionsUpperStarMap A b ((i)^*[A].obj G) ≫
                (Sheaf.Γ _ A).map ((squareUpperStarIso A sq).hom.app G) :=
  ⟨globalSectionsUpperStarMap_id A G, globalSectionsUpperStarMap_comp A a u G,
    globalSectionsUpperStarMap_comp_squareUpperStarIso A sq G,
    fun x x' hx ↦ globalSectionsUpperStarMap_descent A sq G x x' hx⟩

end AlgebraicGeometry.Etale
