abstract sig Account {
	/*name: one Name,
	surname: one Surname,
	username: one Username,
	email: one Email,
	password: one Password*/
}

/*sig Name {
}

sig Surname {
}

sig Email {}
{
	no disj a1, a2 : Account | a1.email = a2.email
}

sig Username {}
{
	no disj a1, a2 : Account | a1.username = a2.username
}

sig Password {
} */

sig Farm {
	area: one Area
} {
	#this.~inspection >= 2
}

sig Post {
} 

sig DailyPlan {
	visits: set Visit
} {
	#visits>=2
}

sig Visit {
	inspection: one Farm
}  

one sig DashBoard {
	farms_dashboard: set Farm
}

sig Thread {
	posts: some Post,
}

one sig Forum {
	threads: set Thread,
}

sig Area {
	farms: some Farm,
}

/*sig PolicyMaker extends Account {
	dashboard: one DashBoard,
}*/

sig Farmer extends Account {
	farm: one Farm,
	forumF: one Forum
}

sig Agronomist extends Account {
	forumA: one Forum,
	areas: one Area,
        dashboard: one DashBoard,
	dailyplan: one DailyPlan
}

fact aboutThread {
	posts in Thread one -> Post
}

fact aboutDashBoard {
	farms_dashboard in DashBoard one -> Farm
}

fact aboutForum {
	threads in Forum one -> Thread
	forumA in Agronomist some -> Forum
	forumF in Farmer  some -> Forum
}

fact aboutFarms {
	visits in DailyPlan one -> Visit
	farm in Farmer one -> Farm
	area = ~farms
}

fact aboutAgron {
	areas in Agronomist one -> Area
	dailyplan in Agronomist one -> DailyPlan
	visits in DailyPlan one -> Visit
}

fact aboutArea {
	farms in Area one -> Farm 
}

/*fun visitArea [ v: Visit , f: Farm] : Area {

}*/

pred show {
}

run show for 4 but 6 Visit, 7 Account, exactly 3 Agronomist
