/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.IntegralHom.Reduction.IntegralHomReductionModels
import WeilConjectures.SixFunctors.IntegralHom.Evaluation.IntegralHomEvaluationTransport

/-! # First-variable naturality of normalized integral evaluation

Source: Stacks Project, sites-cohomology.tex, Lemma 08J9 and its functorial
Hom-total-tensor identification.
(blueprint: lem-sf-integral-hom-evaluation-naturality).
-/

@[expose] public section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe u
open CategoryTheory Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.IntegralHom

/-- The representative-normalized counits form a natural evaluation in the Hom source.
This concerns a single arbitrary ring sheaf and a supplied presentation; it constructs
neither tensor, symmetry nor any scalar-reduction presentation.

Source: Stacks Project, sites-cohomology.tex, Lemma 08J9, proof via functorial
Hom-total-tensor currying; Tags 06YS and 06YU for K-flat representatives.
(blueprint: lem-sf-integral-hom-evaluation-naturality).

Proof: take the closed symmetric monoidal structure of the recorded derived Hom.
Its K-flat comparison and a.representative identify its tensor with a.tensor by
full faithfulness of restriction to the product K-flat localization. Transport its
adjunction across this identification and the symmetry, to the order K tensor
Hom(K,W). To compare this adjunction with a.adjunction, represent K by a K-flat
complex P and W by a K-injective complex I. For every K-flat S and chain map
q:S to Hom(P,I), both inverse transposes are represented by the chain map sending
x tensor z in bidegree (i,j) to (-1)^(ij) q(z)(x). For a this is its evaluation
field; for the transported closed structure it follows from its uncurry_model
and its Koszul symmetry model. The direct-sum tensor inclusions, the sheafification
adjunction and pure tensors detect equality of these chain maps. Hom(P,I) is
K-injective, so chain maps modulo homotopy represent every derived map into it.
Every derived source admits a K-flat representative. Thus the inverse Hom
bijections agree for arbitrary source and target, and their counits agree.
Apply the closed structure's evaluation_naturality. Naturality of the tensor
identification and of the symmetry carries that equation to the displayed one.
This works for unbounded complexes, the zero ring and the empty site; there is
no finite-Tor or constructibility hypothesis. -/
theorem evaluation_naturality (X : Scheme.{u})
    (R : Sheaf (ProEt.topology X) CommRingCat.{u + 1})
    (a : TensorPresentation.{u, u} X R)
    (K K' W : Derived.{u, u} X R) (f : K' ⟶ K) :
    a.tensor.map (Prod.mkHom (𝟙 K')
      ((hom.{u, u} X R).map (Prod.mkHom f.op (𝟙 W)))) ≫
        (a.adjunction K').counit.app W =
      a.tensor.map (Prod.mkHom f (𝟙 _)) ≫ (a.adjunction K).counit.app W := by
  obtain ⟨S, e, hc⟩ := tensorPresentation_counit_transport X R a
  rw [← hc K' W, ← hc K W]
  exact transportedCounit_naturality X R a S e K K' W f

end WeilConjectures.IntegralHom
