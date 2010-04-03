//NOTA: Qualquer referência no seguinte texto a elevadores e andares é pura
//coincidência e não deve ser levada a sério.
open util/ordering[State]
 
abstract sig Local {}

sig State {
	//carruagens e pessoas sao as unicas coisas que mudam de sitio
	localActualDeCarruagem: Carruagem set -> one Paragem,
	localActualDePessoa: Pessoa set -> one Local,
	
	//direccoes que mudam (ter uma direccao em pessoa nao torna desnecessario ter direccao em paragem?)
	direccaoCarruagem: Carruagem set -> one Direccao,
	direccaoParagem: Paragem set -> one Direccao,
	direccaoPessoa: Pessoa set -> one Direccao,

	//proximos destinos da carruagem mudam (ver se tem interesse ter uma lista aqui)
	destinosCarruagem: Carruagem set -> set Paragem
}
 
sig Paragem extends Local {
	seguinte: lone Paragem
}

one sig Inicio extends Local { }
one sig Fim extends Local { }
 
sig Carruagem extends Local{
}
 
sig Pessoa {
	destino: one Paragem
}
 
abstract sig Direccao {}
 
one sig Direita, Esquerda, Nenhuma, Ambas extends Direccao {}
 
//------------------------------------------------------------------------------------------------
//----------------------------------- Restringir "seguinte" ---------------------------------
//------------------------------------------------------------------------------------------------
fact aUltimaParagemLigaSempreAPrimeira
{
	all p1: Paragem, p2: Paragem | p2 in p1.^seguinte
}
 
fact naoHaParagemSeguinteIgualParaDuasParagensDiferentes {
	all p1: Paragem, p2: Paragem, p3:Paragem | 
	(p1 != p3 && (p1.seguinte = p2)) => !(p3.seguinte = p2)
}

fact ambasApenasPodeExistirEmParagem {
	!(Ambas in (State.direccaoCarruagem[Carruagem]  + State.direccaoPessoa[Pessoa]))
}

//------------------------------------------------------------------------------------------------
//------------------------------------------------------------------------------------------------

pred estadoInicial[s: State] {
	all c1: Carruagem, c2: Carruagem | s.localActualDeCarruagem[c1] = s.localActualDeCarruagem[c2]
	s.direccaoParagem[Paragem] = Nenhuma
	s.direccaoPessoa[Pessoa] = Esquerda
	s.direccaoCarruagem[Carruagem] = Nenhuma
	s.localActualDePessoa[Pessoa] = Inicio and s.localActualDePessoa[Pessoa] != Fim
	!(Nenhuma in (s.direccaoPessoa[Pessoa]))
	s.destinosCarruagem.Paragem = none
}

pred estadosSeguintes[s: State] {
	
}

fact inicio {
	estadoInicial[first]
}


//------------------------------------------------------------------------------------------------
//--------------------------------------------- Pred's ------------------------------------------
//------------------------------------------------------------------------------------------------

pred chamada[s,s': State] {
		one p1: Pessoa, par1: Paragem, d1: Direccao, c1: Carruagem | {

//		pré-condicoes		
		p1 in s.localActualDePessoa.Inicio		//a pessoa tem que estar no "local" inicio
		p1.destino != par1								//o destino da pessoa tem que ser diferente do sitio onde chama a carruagem
		d1 != Nenhuma									//a direccao da pessoa não pode ser "nenhuma"
		d1 != Ambas										//nem "ambas"

//		acções
		s'.localActualDePessoa = s.localActualDePessoa ++ (p1 -> par1) 	//coloca a pessoa numa paragem
		s'.direccaoPessoa = s.direccaoPessoa ++ (p1 -> d1)						//a pessoa quer ir numa direccao
		
//		outras condicoes alternativas
		(s.direccaoCarruagem[c1] = d1 or s.direccaoCarruagem[c1] = Nenhuma) and //se o sentido da carruagem for igual ao da pessoa ou esta estiver parada
		(c1 = s.localActualDeCarruagem.par1) =>															//e se existir uma carruagem na paragem onde pessoa foi colocada
		(
				s'.direccaoCarruagem = s.direccaoCarruagem and						//não há alteração na direccão da carruagem
				s'.destinosCarruagem = s.destinosCarruagem							//os destinos das carruagens continuam os mesmos (já que ela não pode partir sem que todas as pessoas que pode levar entrem)

		) else (s.direccaoCarruagem[c1] = d1 or s.direccaoCarruagem[c1] = Nenhuma) => //se houver uma carruagem com o mesmo sentido ou nenhum mas não estiver na paragem onde a pessoa foi colocada
		(	
				s'.direccaoCarruagem = s.direccaoCarruagem and						//não há alterações na direcção da carruagem (irá chegar à paragem da pessoa)
				s'.destinosCarruagem = s.destinosCarruagem + (c1 -> par1)	//adiciona-se o destino à lista da carruagem, para esta ter que passar por lá
		)
		//senão não se faz nada. Espera-se que uma carruagem fique vazia, e mude de direccao

		s.direccaoParagem[par1] = Nenhuma => 
				s'.direccaoParagem = s.direccaoParagem ++ (par1 -> d1)
		else ( 
				(s.direccaoParagem[par1] = Ambas or s.direccaoParagem[par1] = d1) =>
						s'.direccaoParagem = s.direccaoParagem
				else (
						s'.direccaoParagem = s.direccaoParagem ++ (par1 -> Ambas)
				)
		)
		s'.localActualDeCarruagem = s.localActualDeCarruagem
		}
}

pred movimento[s,s': State] {
		one c1: Carruagem | saemPessoas[s,s',c1] || (ninguemMaisPodeSair[s] and entramPessoas[s,s',c1]) || (ninguemMaisPodeSair[s] and ninguemMaisPodeEntrar[s] and movimentaCarruagem[s,s',c1]) 
}

pred saemPessoas[s,s': State, c1: Carruagem] {
		one p1: Pessoa | {
				p1 in s.localActualDePessoa.c1 and 
				s.localActualDeCarruagem[c1] = p1.destino => 
						s'.localActualDePessoa = s.localActualDePessoa ++ (p1 -> Fim) and 
						s'.direccaoPessoa = s.direccaoPessoa ++ (p1 -> Nenhuma)
				else
						s'.direccaoPessoa = s.direccaoPessoa and
						s'.localActualDePessoa = s.localActualDePessoa
		
		s'.localActualDePessoa.c1 = none => 
				s'.direccaoCarruagem = s.direccaoCarruagem ++ (c1 -> Nenhuma) 
		else 
				s'.direccaoCarruagem = s.direccaoCarruagem //neste caso devia ficar a ser a direccao de outra pessoa que esteja na carruagem

		s'.direccaoParagem = s.direccaoParagem
		s'.localActualDeCarruagem = s.localActualDeCarruagem
		s'.destinosCarruagem = s.destinosCarruagem
		}
}

pred ninguemMaisPodeEntrar[s: State] {
		all c1: Carruagem | no p1: Pessoa | 
			s.localActualDePessoa[p1] = s.localActualDeCarruagem[c1] and
			s.localActualDeCarruagem[c1] != p1.destino and 
			(s.direccaoPessoa[p1] = s.direccaoCarruagem[c1] or 
			s.direccaoCarruagem[c1] = Nenhuma)
}

pred ninguemMaisPodeSair[s: State] {
		all c1: Carruagem | no p1: Pessoa |
			p1 in s.localActualDePessoa.c1 and 
			s.localActualDeCarruagem[c1] = p1.destino
}

pred entramPessoas[s,s': State, c1: Carruagem] {
	one p1: Pessoa | {
			s.localActualDePessoa[p1] = s.localActualDeCarruagem[c1] and
			s.localActualDeCarruagem[c1] != p1.destino and 
			(s.direccaoPessoa[p1] = s.direccaoCarruagem[c1] or 
			s.direccaoCarruagem[c1] = Nenhuma)  =>
					s'.localActualDePessoa = s.localActualDePessoa ++ (p1 -> c1) and
					s'.destinosCarruagem = s.destinosCarruagem + (c1 -> p1.destino)
			else
					s'.localActualDePessoa = s.localActualDePessoa and
					s'.destinosCarruagem = s.destinosCarruagem
			
		s.direccaoCarruagem[c1] = Nenhuma => 
				s'.direccaoCarruagem = s.direccaoCarruagem ++ (c1 -> s.direccaoPessoa[p1]) 
		else 
				s'.direccaoCarruagem = s.direccaoCarruagem //neste caso devia ficar a ser a direccao de outra pessoa que esteja na carruagem
		
		s'.localActualDeCarruagem = s.localActualDeCarruagem
		s'.direccaoParagem = s.direccaoParagem
		s'.direccaoPessoa = s.direccaoPessoa
		}
			
}

pred movimentaCarruagem[s,s': State, c1: Carruagem] {
	let p1 = s.localActualDeCarruagem[c1] 
	{
		(s.direccaoCarruagem[c1] = Nenhuma) implies
				(s'.localActualDeCarruagem = s.localActualDeCarruagem) 
		else 
		(s.direccaoCarruagem[c1] = Direita) implies
				(s'.localActualDeCarruagem = s.localActualDeCarruagem ++ (c1 -> p1.seguinte))
		else
		(s.direccaoCarruagem[c1] = Esquerda) implies 
				(s'.localActualDeCarruagem = s.localActualDeCarruagem ++ (c1 -> seguinte.p1))
		s'.destinosCarruagem = s.destinosCarruagem - (c1 -> p1)
	}
	s'.localActualDePessoa = s.localActualDePessoa

	s'.localActualDeCarruagem = s'.destinosCarruagem =>
		s'.direccaoCarruagem = s.direccaoCarruagem ++ (c1 -> Nenhuma)
	else
		s'.direccaoCarruagem = s.direccaoCarruagem

	s'.direccaoParagem = s.direccaoParagem
	s'.direccaoPessoa = s.direccaoPessoa
}
/*
pred movimentacaoDeUmaCarruagem[s, s': State, c1: Carruagem] {
	let p1 = s.localActualDeCarruagem[c1] 
	{
		(s.direccaoCarruagem[c1] = Nenhuma) implies
				(s'.localActualDeCarruagem = s.localActualDeCarruagem) 
		else 
		(s.direccaoCarruagem[c1] = Direita) implies
				(s'.localActualDeCarruagem = s.localActualDeCarruagem ++ (c1 -> p1.seguinte))
		else
		(s.direccaoCarruagem[c1] = Esquerda) implies 
				(s'.localActualDeCarruagem = s.localActualDeCarruagem ++ (c1 -> seguinte.p1))
		s'.destinosCarruagem = s.destinosCarruagem - (c1 -> p1)
	}
	s'.localActualDePessoa = s.localActualDePessoa
	s'.direccaoCarruagem = s.direccaoCarruagem
	s'.direccaoParagem = s.direccaoParagem
	s'.direccaoPessoa = s.direccaoPessoa
}

pred entramPessoas[s, s': State, c1: Carruagem, p1: Pessoa] {
		{ s.localActualDePessoa[p1]  = s.localActualDeCarruagem[c1] and
		s.direccaoPessoa[p1] = s.direccaoCarruagem[c1]} implies {					//se a direccao da pessoa for a mesma da carruagem em que viaja
				s'.localActualDePessoa = s.localActualDePessoa ++ (p1 -> c1)	 		//pessoa entra na carruagem
				s'.direccaoPessoa = s.direccaoPessoa	 												//continua na mesma direccao
				s'.destinosCarruagem = s.destinosCarruagem + (c1 -> p1.destino)//adicionamos o destino da pessoa ao destino da carruagem
				s'.localActualDeCarruagem = s.localActualDeCarruagem						//carruagens estao no mesmo sitio
				(s.direccaoCarruagem[c1] = Nenhuma) implies {
						s'.direccaoCarruagem = s.direccaoCarruagem ++ (c1 -> s.direccaoPessoa[p1])
				} else {
						s'.direccaoCarruagem = s.direccaoCarruagem
				}
				s'.direccaoParagem = s.direccaoParagem
		} else {
				s'.localActualDePessoa = s.localActualDePessoa
				s'.direccaoCarruagem = s.direccaoCarruagem
				s'.direccaoParagem = s.direccaoParagem
				s'.direccaoPessoa = s.direccaoPessoa	
				s'.localActualDeCarruagem = s.localActualDeCarruagem
				s'.destinosCarruagem = s.destinosCarruagem
		}
}
*/
//------------------------------------------------------------------------------------------------
//--------------------------------------- Cheques (em branco ou não) -------------------
//------------------------------------------------------------------------------------------------

//se houver uma chamada, faz-se as modificaçoes de chamada.
//se não houver uma chamada, há movimento.
	//se houver movimento, deixa-se sair uma pessoa ou entrar uma pessoa ou move-se o elevador

fact motor {
	all s : State, s' : s.next | (!chamada[s,s'] and movimento[s,s']) || (chamada[s,s'] and !movimento[s,s'])
}
 
assert cond1 {
	one s: first | all p: Pessoa | s.direccaoPessoa[p] = Nenhuma
}
//check cond1
assert cond2 {
	one s: first | all c: Carruagem | s.direccaoCarruagem[c] = Nenhuma
}
//check cond2
assert cond3 {
	one s: first | all p: Paragem | s.direccaoParagem[p] = Nenhuma
}
//check cond3
assert cond4 {
	all s: State | all c: Carruagem | s.direccaoCarruagem[c] = Nenhuma
}
//check cond4 for 8 but exactly 3 Paragem, exactly 2 Pessoa
assert cond5 {
	no s: State | s.localActualDePessoa.Paragem != none
}
//check cond5 for 6 but exactly 3 Pessoa, exactly 3 Carruagem, exactly 3 Paragem
assert cond6 {
	all s: State, s1: s.next | s.localActualDePessoa = s1.localActualDePessoa
}
//check cond6 for 8 but exactly 3 Pessoa, exactly 3 Carruagem, exactly 3 Paragem
assert condFinal {
	no s: State | (s.localActualDePessoa[Pessoa] = Fim)
}
check condFinal for 3 but exactly 1 Pessoa, exactly 3 Carruagem, exactly 3 Paragem, 9 State
//run {} for 3 but exactly 3 Pessoa, exactly 3 Carruagem, exactly 3 Paragem, exactly 9 State


//coisas a ver
// - carruagem apenas deve parar numa paragem se tiver que largar alguem ou se a paragem estiver com uma chamada na mesma direccao de deslocamento da carruagem
