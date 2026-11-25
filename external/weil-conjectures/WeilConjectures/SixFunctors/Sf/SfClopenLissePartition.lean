/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleLocallyConstantSheafOfUniverses
public import Mathlib.AlgebraicGeometry.OpenImmersion
import WeilConjectures.SixFunctors.Sf.SfClopenCoverGeometry
import WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantModuleRestriction
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.Algebra.Field.ULift

/-! # Simultaneous finite lisse trivialization on clopen pieces

Source: Stacks Project, Tags 098F and 09C3.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall

universe t u v
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme
namespace WeilConjectures

private def constant_model_iso (T : Scheme.{t}) (Λ : Type u) [CommRing Λ]
    (U : T.ProEt) (M N : ModuleCat.{max u (t + 1)} (ULift.{t + 1} Λ)) (e : M ≅ N) :
    proEtaleConstantModuleSheafOverOfUniverses T Λ U M ≅
      proEtaleConstantModuleSheafOverOfUniverses T Λ U N := by
  let : EssentiallySmall.{max u (t + 1)} (Over U) := essentiallySmallSelf _
  let : HasSheafify ((ProEt.topology T).over U) AddCommGrpCat.{max u (t + 1)} :=
    hasSheafifyEssentiallySmallSite _ _
  let : ((ProEt.topology T).over U).WEqualsLocallyBijective
      AddCommGrpCat.{max u (t + 1)} :=
    GrothendieckTopology.WEqualsLocallyBijective.ofEssentiallySmall _
  have := (proEtaleConstantRingUnit_over_locallyBijectiveOfUniverses T Λ U).1
  have := (proEtaleConstantRingUnit_over_locallyBijectiveOfUniverses T Λ U).2
  let p : proEtaleConstantModulePresheafOfUniverses (Over U) Λ M ≅
      proEtaleConstantModulePresheafOfUniverses (Over U) Λ N :=
    { hom := { app _ := e.hom }
      inv := { app _ := e.inv } }
  exact (PresheafOfModules.sheafification _).mapIso p

/-- Finitely many locally constant finite-dimensional module sheaves on an affine
categorically weakly contractible scheme have a common finite clopen free partition.

Source: Stacks Project, Tags 098F and 09C3
(blueprint: lem-sf-clopen-lisse-partition).
Proof: for each sheaf form the sieve of arrows on which it is constant with a finite
model. Constant-model restriction makes it downward closed, and the given trivializing
cover makes it covering. Intersect these finitely many sieves, using the top sieve for
an empty family. The categorical clopen-cover refinement gives a common partition.
Choose a finite basis of each model and sheafify the corresponding linear isomorphism
to obtain the displayed free models. Each piece is closed in the compact affine target,
so compact. Zero ranks and empty pieces are included. -/
theorem sf_clopen_lisse_partition (T : Scheme.{t}) [IsAffine T]
    (hweak : ∀ (A B : Sheaf (ProEt.topology T) (Type (max u (t + 1))))
      (f : A ⟶ B), Epi f → Function.Surjective (f.hom.app (op (ProEt.mk (𝟙 T)))))
    (Λ : Type u) [Field Λ] (J : Type v) [Finite J]
    (F : J → SheafOfModules.{max u (t + 1)}
      ((sheafCompose (ProEt.topology T)
        (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})).obj
          ((constantSheaf (ProEt.topology T) CommRingCat.{max u (t + 1)}).obj
            (CommRingCat.of (ULift.{t + 1} Λ)))))
    (hF : ∀ j, IsLocallyConstantProEtaleModuleSheafWithModelsOfUniverses T Λ
      (fun N ↦ Module.Finite (ULift.{t + 1} Λ) N) (F j)) :
    ∃ (n : ℕ) (U : Fin n → T.Opens), iSup U = ⊤ ∧
      Pairwise (fun i j ↦ Disjoint (U i) (U j)) ∧
      ∀ i, IsClosed (U i : Set T) ∧ IsCompact (U i : Set T) ∧
        ∀ j, ∃ r : ℕ, Nonempty ((F j).over (ProEt.mk (U i).ι) ≅
          proEtaleConstantModuleSheafOverOfUniverses T Λ (ProEt.mk (U i).ι)
            (ModuleCat.of (ULift.{t + 1} Λ) (Fin r → ULift.{t + 1} Λ))) := by
  classical
  let Q (j : J) : Sieve (ProEt.mk (𝟙 T)) :=
    { arrows := fun V _ ↦ ∃ M : ModuleCat.{max u (t + 1)} (ULift.{t + 1} Λ),
        Module.Finite (ULift.{t + 1} Λ) M ∧
          Nonempty ((F j).over V ≅ proEtaleConstantModuleSheafOverOfUniverses T Λ V M)
      downward_closed := by
        rintro V W f ⟨M, hM, e⟩ a
        exact ⟨M, hM, proEtaleConstantModule_restrict T Λ (F j) V W a M e⟩ }
  have hQ (j : J) : Q j ∈ ProEt.topology T (ProEt.mk (𝟙 T)) := by
    obtain ⟨I, V, f, hf, hlocal⟩ := hF j
    apply (ProEt.topology T).superset_covering _
      (Precoverage.generate_mem_toGrothendieck hf)
    apply (Sieve.generate_le_iff _ _).mpr
    rintro V' f' ⟨i⟩
    exact hlocal i
  let : Fintype J := Fintype.ofFinite J
  have hfin (s : Finset J) : s.inf Q ∈ ProEt.topology T (ProEt.mk (𝟙 T)) := by
    induction s using Finset.induction_on with
    | empty => simp
    | @insert j s hj ih =>
      simpa only [Finset.inf_insert] using (ProEt.topology T).intersection_covering (hQ j) ih
  obtain ⟨n, U, hclosed, hdisjoint, hcover, hlocal⟩ :=
    (sf_clopen_cover_geometry.{t, u, u} T hweak).1 _ (hfin Finset.univ)
  refine ⟨n, U, hcover, hdisjoint, fun i ↦ ⟨hclosed i, (hclosed i).isCompact, ?_⟩⟩
  intro j
  have hj : Q j (ProEt.ofOpenImmersionHom (ProEt.mk (𝟙 T)) (U i).ι) :=
    (Finset.inf_le (Finset.mem_univ j) : Finset.univ.inf Q ≤ Q j) _ (hlocal i)
  obtain ⟨M, hM, ⟨e⟩⟩ := hj
  let := hM
  let r := Module.finrank (ULift.{t + 1} Λ) M
  let b := Module.finBasis (ULift.{t + 1} Λ) M
  let eM : M ≅ ModuleCat.of (ULift.{t + 1} Λ) (Fin r → ULift.{t + 1} Λ) :=
    b.equivFun.toModuleIso
  exact ⟨r, ⟨e ≪≫ constant_model_iso T Λ _ M _ eM⟩⟩

end WeilConjectures
