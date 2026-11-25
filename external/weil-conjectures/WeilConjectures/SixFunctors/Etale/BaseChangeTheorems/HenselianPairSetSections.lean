/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.RingTheory.Henselian
public import WeilConjectures.AlgebraicGeometry.EtaleSheaves
public import WeilConjectures.AlgebraicGeometry.Sites.UpperStarSections
import WeilConjectures.AlgebraicGeometry.GabberH0EtaleCriterion
import WeilConjectures.AlgebraicGeometry.HenselianConnectedness
import WeilConjectures.AlgebraicGeometry.ZariskiClosedImmersionConnectedRestriction
import WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.HenselianPairSections

/-!
# Sections of étale sheaves of sets over a proper scheme over a henselian pair

Let `(A, I)` be a henselian pair, `p : Y ⟶ Spec A` proper and `i : Y₀ ⟶ Y` the closed fibre
over `Spec A/I`. For every sheaf of sets `F` on the small étale site of `Y`, restriction
`Γ(Y, F) ⟶ Γ(Y₀, i^* F)` is bijective, naturally in `F` [Stacks 0A0C].

Global sections are the sections over the terminal étale schemes `Scheme.Etale.mk (𝟙 Y)` and
`Scheme.Etale.mk (𝟙 Y₀)`, and `i^*` is the inverse image `Scheme.etaleSetPullback i` of
sheaves of sets.

## Main definitions

- `AlgebraicGeometry.Etale.setGlobalSectionsUpperStarMap`: the restriction
  `Γ(Y, F) ⟶ Γ(Y₀, i^* F)` for a sheaf of sets `F`.

## Main statements

- `AlgebraicGeometry.Etale.setGlobalSectionsUpperStarMap_naturality`: the restriction is
  natural in `F`.
- `AlgebraicGeometry.Etale.bijective_setGlobalSectionsUpperStarMap_of_henselianRing`: the
  comparison over a henselian pair.

## Implementation details

The proof is Gabber's criterion `AlgebraicGeometry.gabber_h0_etale_criterion` [Stacks 09ZF]:
it suffices that restriction to the closed fibre is bijective on global sections of Zariski
sheaves of sets on `Y` and on every finite `Y`-scheme `Y'`. These follow from the spectral
restriction lemma [Stacks 09ZG] (`AlgebraicGeometry.zariski_restriction_universe_transport`),
since every irreducible closed subset of `Y'`, which is proper over `A`, meets the closed fibre
in a nonempty connected set (`AlgebraicGeometry.Scheme.Hom.isConnected_inter_preimage_zeroLocus`,
[Stacks 0A0B]).

## References

- Stacks Project, Lemma 59.91.2, <https://stacks.math.columbia.edu/tag/0A0C>
- Stacks Project, Lemma 59.82.2, <https://stacks.math.columbia.edu/tag/09ZF>
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry.Etale

section Restriction

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- The adjunction `f^* ⊣ f_*` for étale sheaves of sets. -/
noncomputable abbrev _root_.AlgebraicGeometry.Scheme.etaleSetPullbackAdjunction :
    Scheme.etaleSetPullback f ⊣
      (MorphismProperty.Over.pullback @Etale ⊤ f).sheafPushforwardContinuous (Type (u + 1))
        (Y.smallGrothendieckTopology @Etale) (X.smallGrothendieckTopology @Etale) :=
  Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
    (MorphismProperty.Over.pullback @Etale ⊤ f) (Type (u + 1))
    (Y.smallGrothendieckTopology @Etale) (X.smallGrothendieckTopology @Etale)

/-- The terminal étale `X`-scheme maps to the base change along `f` of the terminal étale
`Y`-scheme. -/
noncomputable abbrev terminalToPullbackTerminal :
    Scheme.Etale.mk (𝟙 X) ⟶ (MorphismProperty.Over.pullback @Etale ⊤ f).obj
      (Scheme.Etale.mk (𝟙 Y)) :=
  homToPullback f (U := Scheme.Etale.mk (𝟙 Y)) (V := Scheme.Etale.mk (𝟙 X)) f
    ((Category.comp_id _).trans (Category.id_comp _).symm)

instance : IsIso (terminalToPullbackTerminal f) := by
  have : Mono ((MorphismProperty.Over.pullback @Etale ⊤ f).obj (Scheme.Etale.mk (𝟙 Y))).hom :=
    inferInstanceAs (Mono (pullback.snd (𝟙 Y) f))
  let g : (MorphismProperty.Over.pullback @Etale ⊤ f).obj (Scheme.Etale.mk (𝟙 Y)) ⟶
      Scheme.Etale.mk (𝟙 X) :=
    MorphismProperty.Over.homMk (pullback.snd (𝟙 Y) f) (Category.comp_id _)
  exact ⟨g, Scheme.Etale.hom_ext_mk_id _ _, MorphismProperty.Over.Hom.ext ((cancel_mono _).1
    ((MorphismProperty.Over.w _).trans (MorphismProperty.Over.w _).symm))⟩

/-- The restriction `Γ(Y, F) ⟶ Γ(X, f^* F)` of global sections of an étale sheaf of sets `F`
along `f : X ⟶ Y`: the unit of `f^* ⊣ f_*` at the terminal étale `Y`-scheme, followed by the
identification of its base change with the terminal étale `X`-scheme. -/
noncomputable def setGlobalSectionsUpperStarMap (F : Sheaf Y.smallEtaleTopology (Type (u + 1))) :
    F.obj.obj (op (Scheme.Etale.mk (𝟙 Y))) ⟶
      ((Scheme.etaleSetPullback f).obj F).obj.obj (op (Scheme.Etale.mk (𝟙 X))) :=
  ((Scheme.etaleSetPullbackAdjunction f).unit.app F).hom.app (op (Scheme.Etale.mk (𝟙 Y))) ≫
    ((Scheme.etaleSetPullback f).obj F).obj.map (terminalToPullbackTerminal f).op

/-- The restriction of global sections of étale sheaves of sets is natural in the sheaf. -/
lemma setGlobalSectionsUpperStarMap_naturality {F F' : Sheaf Y.smallEtaleTopology (Type (u + 1))}
    (φ : F ⟶ F') :
    φ.hom.app (op (Scheme.Etale.mk (𝟙 Y))) ≫ setGlobalSectionsUpperStarMap f F' =
      setGlobalSectionsUpperStarMap f F ≫
        ((Scheme.etaleSetPullback f).map φ).hom.app (op (Scheme.Etale.mk (𝟙 X))) := by
  have hu := congrArg (fun ψ ↦ ψ.hom.app (op (Scheme.Etale.mk (𝟙 Y))))
    ((Scheme.etaleSetPullbackAdjunction f).unit.naturality φ)
  dsimp at hu
  simp only [setGlobalSectionsUpperStarMap, ← Category.assoc, hu]
  simp only [Category.assoc]
  congr 1
  exact (((Scheme.etaleSetPullback f).map φ).hom.naturality _).symm

/-- The restriction of global sections along `f` is bijective if and only if the unit of
`f^* ⊣ f_*` is bijective at the terminal étale scheme. -/
lemma bijective_setGlobalSectionsUpperStarMap_iff
    (F : Sheaf Y.smallEtaleTopology (Type (u + 1))) :
    Function.Bijective (setGlobalSectionsUpperStarMap f F) ↔
      Function.Bijective (((Scheme.etaleSetPullbackAdjunction f).unit.app F).hom.app
        (op (Scheme.Etale.mk (𝟙 Y)))) := by
  have : IsIso (((Scheme.etaleSetPullback f).obj F).obj.map
      (terminalToPullbackTerminal f).op) := inferInstance
  exact ((isIso_iff_bijective _).1 this).of_comp_iff' _

end Restriction

/-- Let `(A, I)` be a henselian pair, `p : Y ⟶ Spec A` proper and `i : Y₀ ⟶ Y` the closed
fibre over `Spec (A ⧸ I)`. For every sheaf of sets `F` on the small étale site of `Y`, the
restriction `Γ(Y, F) ⟶ Γ(Y₀, i^* F)` is bijective. -/
@[stacks 0A0C]
theorem bijective_setGlobalSectionsUpperStarMap_of_henselianRing {A : Type u} [CommRing A]
    (I : Ideal A) [HenselianRing A I] {Y Y₀ : Scheme.{u}} (p : Y ⟶ Spec (.of A)) [IsProper p]
    (i : Y₀ ⟶ Y) (p₀ : Y₀ ⟶ Spec (.of (A ⧸ I)))
    (h : IsPullback i p₀ p (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))))
    (F : Sheaf Y.smallEtaleTopology (Type (u + 1))) :
    Function.Bijective (setGlobalSectionsUpperStarMap i F) := by
  have : IsClosedImmersion i := isClosedImmersion_of_isPullback I p i p₀ h
  have : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace p
  have : QuasiSeparatedSpace Y := quasiSeparatedSpace_of_quasiSeparated p
  have hconn (X' : Scheme.{u}) (g : X' ⟶ Y) [IsFinite g] (C : Set X') (hC : IsClosed C)
      (hC' : IsIrreducible C) : IsConnected (C ∩ g ⁻¹' Set.range i) := by
    rw [range_eq_preimage_zeroLocus_of_isPullback I p i p₀ h]
    exact (g ≫ p).isConnected_inter_preimage_zeroLocus I hC hC'
  have hZar := zariski_restriction_universe_transport i (fun x ↦ by
    simpa using hconn Y (𝟙 Y) (closure ({x} : Set Y)) isClosed_closure
      isIrreducible_singleton.closure)
  have hFinite (X' : Scheme.{u}) (g : X' ⟶ Y) [IsFinite g] := by
    have : CompactSpace X' := QuasiCompact.compactSpace_of_compactSpace g
    have : QuasiSeparatedSpace X' := quasiSeparatedSpace_of_quasiSeparated g
    exact zariski_restriction_universe_transport (pullback.snd i g) (fun x ↦ by
      rw [Scheme.Pullback.range_snd]
      exact hconn X' g (closure ({x} : Set X')) isClosed_closure
        isIrreducible_singleton.closure)
  rw [bijective_setGlobalSectionsUpperStarMap_iff]
  exact gabber_h0_etale_criterion i hZar hFinite F

end AlgebraicGeometry.Etale
