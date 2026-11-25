/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.RingTheory.NoetherianLocalModelTower
public import Mathlib.Algebra.Category.Ring.Colimits
public import Mathlib.Algebra.Category.Grp.Colimits
public import Mathlib.CategoryTheory.Category.Preorder
public import Mathlib.RingTheory.Localization.Defs
import WeilConjectures.RingTheory.NoetherianLocalModelTowerFiberLocalization
import WeilConjectures.RingTheory.NoetherianLocalModelTowerFiberColimit

/-!
# Categorical presentation of the closed-fibre system

Source: Stacks Project, Algebra, Tag 00R7 (lemma-criterion-flatness-fibre),
the paragraph beginning with the colimit of the maximal ideals.
-/

@[expose] public section

universe u v w t

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

namespace Module

/-- The closed-fibre quotients form a local Noetherian diagram with localization
transitions and module base-change transitions, and its colimit is the closed fibre.
There is no flatness assumption or flat-stage conclusion in this construction lemma.

Source: Stacks Project, Algebra, Tag 00R7 (lemma-criterion-flatness-fibre), the paragraph
beginning with the colimit of the maximal ideals, before the second use of Tag 00R6.
(blueprint: lem-weil-pbc-noetherian-local-model-tower-fiber-diagram)

Proof:
1. Put m_i = maximalIdeal R_i, A_i = S_i/m_i S_i, B_i = T_i/m_i T_i, and
   D_i = B_i tensor over T_i with N_i. Use ULift for the module universe if necessary.
   Local homomorphisms pull maximal ideals back to maximal ideals. The transition
   maps therefore descend to these quotients. On D_i send a pure tensor b tensor n
   to the tensor of the image of b and nmap n. The original system laws, checked
   on quotient representatives and pure tensors, give functor laws, the commuting
   ring squares, and semilinearity. The extended ideals lie in the maximal ideals
   of S_i and T_i, so A_i and B_i are Noetherian local rings, their maps are local,
   and D_i is finite over B_i by quotient base change of X.finite.
2. Quotient the localization specified by X.fibreTransition by the image of m_j.
   Its source is B_i tensor over A_i with A_j: elements of m_i already vanish,
   and quotienting by m_j in the second factor imposes the remaining relations.
   Localization commutes with this quotient, giving hloc with the displayed formula.
   Quotient X.moduleTransition by m_j and use tensor associativity to obtain hbase,
   with its displayed formula on pure tensors. Tensor over the quotient identifies
   D_i with A_i tensor over S_i with N_i, compatibly with the A_i action. These
   identifications are the final stage ring and additive equivalences below.
3. The limit maps descend to S/m_R S, T/m_R T, and (S/m_R S) tensor over S with M.
   They give compatible cocones and scalar actions. Every quotient representative
   comes from a stage, by the tower's surjectivity fields. If a representative maps
   to zero, express its image as a finite sum of multiples of elements of m_R.
   Represent those finitely many coefficients and module elements at a common stage.
   Locality of R_i to R puts each lifted coefficient in m_i. Descend the equality
   by the tower's eventual-equality fields at a further common stage; there the
   quotient representative is zero. For module tensors use their identification
   with the module quotient and the same finite-sum argument. Thus the cocones are
   colimits. The induced comparison maps are bijective, hence ring and additive
   equivalences. Their formulas on representatives show that the colimit scalar
   action restricts along psi to the closed-fibre action. This gives the final
   limit equivalences and their scalar compatibility. No flatness is used here.
-/
theorem NoetherianLocalModelTower.exists_fiber_diagram
    {R : Type u} {S : Type v} {S' : Type w} {M : Type t}
    [CommRing R] [CommRing S] [CommRing S'] [IsLocalRing R] [AddCommGroup M]
    [Algebra R S] [Algebra S S'] [Module S' M] [Module S M]
    [IsScalarTower S S' M]
    (X : NoetherianLocalModelTower R S S' M) :
    letI := X.preorder
    letI := X.commR
    letI := X.commS
    letI := X.localR
    letI := X.algRS
    letI := X.addN
    letI := X.moduleS
    ∃ (A B : X.ι ⥤ CommRingCat.{max u v w})
      (D : X.ι ⥤ AddCommGrpCat.{max u v w t})
      (act : ∀ i, Module (B.obj i) (D.obj i)),
    letI := act
    ∃ (φ : ∀ i, A.obj i →+* B.obj i)
      (ψ : (colimit A : CommRingCat.{max u v w}) →+*
        (colimit B : CommRingCat.{max u v w}))
      (limitAct : Module (colimit B : CommRingCat.{max u v w})
        (colimit D : AddCommGrpCat.{max u v w t})),
    letI := limitAct
    (∀ i, IsLocalRing (A.obj i)) ∧
    (∀ i, IsLocalRing (B.obj i)) ∧
    (∀ i, IsNoetherianRing (A.obj i)) ∧
    (∀ i, IsNoetherianRing (B.obj i)) ∧
    (∀ i, Module.Finite (B.obj i) (D.obj i)) ∧
    (∀ i, IsLocalHom (φ i)) ∧
    (∀ (i j : X.ι) (f : i ⟶ j), IsLocalHom (A.map f).hom) ∧
    (∀ (i j : X.ι) (f : i ⟶ j), IsLocalHom (B.map f).hom) ∧
    (∀ (i j : X.ι) (f : i ⟶ j),
      (B.map f).hom.comp (φ i) = (φ j).comp (A.map f).hom) ∧
    (∀ (i j : X.ι) (f : i ⟶ j) (b : B.obj i) (x : D.obj i),
      (D.map f).hom (b • x) = (B.map f).hom b • (D.map f).hom x) ∧
    (∀ i, ψ.comp (colimit.ι A i).hom = (colimit.ι B i).hom.comp (φ i)) ∧
    (∀ (i : X.ι) (b : B.obj i) (x : D.obj i),
      (colimit.ι D i).hom (b • x) = (colimit.ι B i).hom b • (colimit.ι D i).hom x) ∧
    (∀ (i j : X.ι) (f : i ⟶ j),
      letI := (φ i).toAlgebra
      letI := (A.map f).hom.toAlgebra
      ∃ (q : B.obj i ⊗[A.obj i] A.obj j →+* B.obj j)
        (U : Submonoid (B.obj i ⊗[A.obj i] A.obj j)),
        (∀ (b : B.obj i) (a : A.obj j),
          q (b ⊗ₜ[A.obj i] a) = (B.map f).hom b * φ j a) ∧
        (letI := q.toAlgebra; IsLocalization U (B.obj j))) ∧
    (∀ (i j : X.ι) (f : i ⟶ j),
      letI := (B.map f).hom.toAlgebra
      ∃ e : (B.obj j ⊗[B.obj i] D.obj i) ≃ₗ[B.obj j] D.obj j,
        ∀ (b : B.obj j) (x : D.obj i),
          e (b ⊗ₜ[B.obj i] x) = b • (D.map f).hom x) ∧
    (∀ i, ∃
      (eA : A.obj i ≃+*
        (X.S₀ i ⧸ Ideal.map (algebraMap (X.R₀ i) (X.S₀ i))
          (IsLocalRing.maximalIdeal (X.R₀ i))))
      (eD : D.obj i ≃+
        ((X.S₀ i ⧸ Ideal.map (algebraMap (X.R₀ i) (X.S₀ i))
          (IsLocalRing.maximalIdeal (X.R₀ i))) ⊗[X.S₀ i] X.N₀ i)),
      letI := Module.compHom (D.obj i) (φ i)
      ∀ a x, eD (a • x) = eA a • eD x) ∧
    (∃
      (eA : (colimit A : CommRingCat.{max u v w}) ≃+*
        (S ⧸ Ideal.map (algebraMap R S) (IsLocalRing.maximalIdeal R)))
      (eD : (colimit D : AddCommGrpCat.{max u v w t}) ≃+
        ((S ⧸ Ideal.map (algebraMap R S) (IsLocalRing.maximalIdeal R)) ⊗[S] M)),
      letI := Module.compHom (colimit D : AddCommGrpCat.{max u v w t}) ψ
      ∀ a x, eD (a • x) = eA a • eD x) := by
  let := X.preorder
  let := X.commR
  let := X.commS
  let := X.localR
  let := X.algRS
  let := X.addN
  let := X.moduleS
  let := X.fiberAct
  have hloc := X.fiber_localization
  obtain ⟨limitAct, ⟨hsem, hlim⟩, _⟩ := X.fiber_colimit
  refine ⟨X.fiberA, X.fiberB, X.fiberD, X.fiberAct,
    X.fiberφ, X.fiberψ, limitAct, X.fiberA_local, X.fiberB_local,
    X.fiberA_noetherian, X.fiberB_noetherian, X.fiberD_finite,
    X.fiberφ_local, X.fiberA_map_local, X.fiberB_map_local,
    X.fiber_square, X.fiberD_map_smul, X.fiberψ_comp_ι,
    hsem, hloc, X.fiber_module_baseChange, ?_, hlim⟩
  intro i
  exact ⟨RingEquiv.refl _, X.fiberDEquiv i, X.fiberDEquiv_smul i⟩

end Module
