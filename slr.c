#include<stdio.h>
#include<ctype.h>
#include<stdlib.h>
#include<string.h>

#define SHIFT 200
#define REDUCE 300
#define AUGMENT 'S'


typedef struct st {
	char n_t;
	char in[25];
}st;
typedef struct state {
	int id;
	char set[25][25];
}state;
typedef struct node_int {
	int data;
	struct node_int *next;
}node_int;
typedef struct stack_int {
	node_int* top;
}stack_int;
typedef struct node {
	char data;
	struct node *next;
}node;
typedef struct stack {
	node* top;
}stack;


char production[25][25]; //production rule
char closure[25][25];
char tm[25][25];
st first[25];  //set of first
st follow[25]; //set of follow
state canonical[20];  ///Canonical set
char nonterminal[25]; //nonterminal set
char terminal[25];//terminal set
int count; //number of production
int col_idx = 0;
int table[25][25]; ///table struct shift=200 reduce =300   ex) r1=301 //accept값은 -1  
char clo[25][25]; //LR(0) item of production 

void stackinit(stack* stack) {
	stack->top = NULL;
}
void push(char data, stack* stack) {
	node *node_s = (node*)malloc(sizeof(node));
	node_s->data = data;
	node_s->next = NULL;
	if (stack->top == NULL)
		stack->top = node_s;
	else {
		node_s->next = stack->top;
		stack->top = node_s;
	}
}
char pop(stack* stack) {
	char data;
	node* temp = stack->top;
	if (stack->top == NULL) {
		printf("Stack is Empty");
		return -1;
	}
	else {
		data = (*stack->top).data;
		stack->top = (*stack->top).next;
		free(temp);
		return data;
	}
}


void stackinit_int(stack_int* stack) {
	stack->top = NULL;
}
void push_int(int data, stack_int* stack) {
	node_int *node_s = (node_int*)malloc(sizeof(node_int));
	node_s->data = data;
	node_s->next = NULL;
	if (stack->top == NULL)
		stack->top = node_s;
	else {
		node_s->next = stack->top;
		stack->top = node_s;
	}
}
int pop_int(stack_int* stack) {
	int data;
	node_int* temp = stack->top;
	if (stack->top == NULL) {
		printf("Stack is Empty");
		return -1;
	}
	else {
		data = (*stack->top).data;
		stack->top = (*stack->top).next;
		free(temp);
		return data;
	}
}


int comparest(st s1[], st s2[])
{
	int sum = 0;
	for (int i = 0; i < 25; i++)
	{
		if (!strcmp(s1[i].in, s2[i].in))
			sum += 0;
		else
			sum += 1;
	}
	return sum;
}

void copyst(st s1[], st s2[])
{
	for (int i = 0; i < 25; i++)
	{

		strcpy(s1[i].in, s2[i].in);
		s1[i].n_t = s2[i].n_t;
	}
}

int comparestate(state s1, state s2)
{
	int i;
	if (s1.id != s2.id)
		return 0;
	for (i = 0; i < s1.id; i++)
	{
		if (strcmp(s1.set[i], s2.set[i]) != 0)
			return 0;
	}
	return 1;

}
int indexst(st s1[], char a)
{
	for (int i = 0; i<25; i++)
	{
		if (s1[i].n_t == a)
			return i;
	}
}

void arrayunion(char Result[], char val)
{
	int i;
	for (i = 0; Result[i] != '\0'; i++) {
		if (Result[i] == val)
			return;
	}
	Result[i] = val;
	Result[i + 1] = '\0';
}
void find_first(char Result[], char c)
{
	int i, j, k, l;
	char subResult[25];
	int foundEpsilon;
	int state = 0;
	subResult[0] = '\0';
	Result[0] = '\0';
	
	if (!(isupper(c)))  //c is terminal-> put c in result
	{
		arrayunion(Result, c);
		return;
	}

	for (i = 0; i<count; i++)  // c is nonterminal
	{
		if (production[i][0] == c)    //ex E->E*T|T 
		{
			if (production[i][2] == '#') // c-># , add the # to first
				arrayunion(Result, '#');
			else {
				j = 2;
				while (production[i][j] != '\0')
				{
					foundEpsilon = 0;
					state = 0;
					for (l = 0; Result[l] != '\0'; l++){ 
						if (Result[l] == '#')
							state = 1;
					}

					if (state == 1 && production[i][0] == production[i][2]){
						j++;
						continue;
					}
					else if (production[i][0] == production[i][2]){
						break;
					}

					find_first(subResult, production[i][j]);  // FIRST of production[i][j] put in FIRST(C) 
					for (k = 0; subResult[k] != '\0'; k++)
						arrayunion(Result, subResult[k]);
					for (k = 0; subResult[k] != '\0'; k++)
					if (subResult[k] == '#'){
						foundEpsilon = 1;
						break;
					}
					if (!foundEpsilon)
						break;
					j++;


				}
			}
		}
	}
	return;
}
void find_follow(char result[], char ch)
{
	int i = 0, index, j, k, epsilon = 0, temp1, l;
	int length;
	char subresult[25], subresult1[25];
	subresult[0] = '\0';
	subresult1[0] = '\0';

	index = indexst(follow, ch);

	for (i = 0; i < count; i++)
	{
		j = strlen(production[i]);
		for (j = 2; j < strlen(production[i]); j++)
		{
			if (production[i][j] == ch)
			{
				if (production[i][j + 1] != '\0')
				{
					find_first(subresult, production[i][j + 1]);   //S->ABC FOLLOW(A)<-first(B)
					for (k = 0; subresult[k] != '\0'; k++) {
						if (subresult[k] == '#') {
							epsilon = 1;
						}
						else {
							arrayunion(follow[index].in, subresult[k]);
						}
					}
					subresult[0] = '\0';
					if (epsilon == 1)
					{
						l = 2;
						while (production[i][j + l] != '\0' && epsilon == 1) {     //S->ABC 에서 B,C 모두 nullable or B nullable //S->ABC B and C are nullable or B is nullable
							if (production[i][j + l] != '\0')
							{
								epsilon = 0;
								find_first(subresult, production[i][j + l]);
								for (k = 0; subresult[k] != '\0'; k++) {
									if (subresult[k] == '#') {
										epsilon = 1;
									}
									else {
										arrayunion(follow[index].in, subresult[k]);
									}
								}
							}
							l++;
						}
					}
				}

				if (production[i][j + 1] == '\0' && ch != production[i][0] || epsilon == 1)  //S->ABC에서 C가 nullable일경우 나 S-AB일경우 Follow(B) // C is nullable or follow(B)
				{
					if (ch == production[i][j])
					{
						temp1 = indexst(follow, production[i][0]);
						for (k = 0; follow[temp1].in[k] != '\0'; k++) {
							arrayunion(follow[index].in, follow[temp1].in[k]);
						}
					}
				}
				epsilon = 0;

			}

		}
	}
}

void closureset() {
	char temp;
	int i, j = 3, k, l;
	int index = 0, idx = 0;
	char ch;

	clo[0][0] = AUGMENT;    //input the augmented production rule
	clo[0][1] = '>';
	clo[0][2] = '.';
	clo[0][3] = production[0][0];
	clo[0][4] = '\0';

	for (i = 0; i < count; i++)
	{
		strcpy(clo[i + 1], production[i]);
		for (k = strlen(production[i]); k >= 2; k--) {
			clo[i + 1][k + 1] = clo[i + 1][k];
		}
		clo[i + 1][2] = '.';
	}  // into the dotsymbol

	strcpy(closure[index++], clo[0]);

	for (i = 0; i < count + 1; i++)
	{
		if (strlen(closure[i]) != 0)
		{
			ch = closure[i][j];
			for (int m = 0; strlen(closure[m]) != 0; m++)
			{
				temp = closure[m][0];
				if (ch == temp) {
					idx = 1;
				}
			}
		}
		if (idx == 1)
		{
			idx = 0;
			continue;
		}
		for (k = 0; k <= count; k++)
		{
			if (ch == clo[k][0]) {
				strcpy(closure[index++], clo[k]);
			}
		}
	}

	for (int i = 0; strlen(closure[i]) != 0; i++)   //find the I0
	{
		strcpy(canonical[0].set[i], closure[i]);
	}
	canonical[0].id = i;
	col_idx++;
}

int gotopro(int index, char ch)//i0,L
{
	state temp;
	stack s;
	int sema = 0;
	char ex;
	char tempclo[25][25];
	int con = 0;
	int dot = 0;
	char ep_tmp;
	int rt_idx = -1;
	int i, j;
	temp.id = 0;
	stackinit(&s);

	for (i = 0; i <= canonical[index].id; i++)
	{
		for (j = 0; j < strlen(canonical[index].set[i]) != 0; j++)
		{
			if (canonical[index].set[i][j] == '.'&&j != strlen(canonical[index].set[i]) - 1)
			{
				if (canonical[index].set[i][j + 1] == ch)
				{
					temp.id += 1;
					strcpy(temp.set[con], canonical[index].set[i]);
					temp.set[con][j] = temp.set[con][j + 1];
					temp.set[con][j + 1] = '.';
					con++;
					if (temp.set[con - 1][j + 2] <= 90 && temp.set[con - 1][j + 2] >= 65)
					{
						ex = temp.set[con - 1][j + 2];
						push(ex, &s);
						while (s.top != NULL)
						{
							ex = pop(&s);
							//if (ex != '#')
							//{
							for (int k = 0; strlen(clo[k]) != 0; k++)
							{
								if (clo[k][0] == ex)
								{
									for (int m = 0; m < con; m++) //if clo[k] already in temp.set => seam=1
									{
										if (strcmp(temp.set[m], clo[k]) == 0)
											sema = 1;
									}
									if (sema == 0) //if sema==0 put the clo[k] into temp.set
									{
										temp.id++;
										strcpy(temp.set[con++], clo[k]);
										if (clo[k][3] >= 65 && clo[k][3] <= 90)
										{
											if (ex != clo[k][3])
												push(clo[k][3], &s); //put the stack nonterminal
										}
									}
									sema = 0;
								}
							}
							for (int l = 0; l<temp.id; l++)
							{
								for (int m = 2; m<strlen(temp.set[l])-1; m++)
								{
									if (temp.set[l][m] == '.'&&temp.set[l][m+1]=='#')
									{
										ep_tmp = temp.set[l][m + 1];
										temp.set[l][m + 1] = '.';
										temp.set[l][m] = ep_tmp;
									}
								}
							}

						}
						//}
					}
				}
			}
		}
	}
	if (temp.id != 0)
	{
		for (j = 0; j < col_idx; j++)
		{
			if (comparestate(temp, canonical[j]) == 1)
			{
				rt_idx = j;
				return rt_idx;
			}

		}
		if (rt_idx == -1)
		{
			for (i = 0; i<temp.id; i++) {
				strcpy(canonical[col_idx].set[i], temp.set[i]);
			}
			canonical[col_idx].id = temp.id;

			col_idx++;
			return col_idx - 1;
		}
	}
	return -2;

}


int main(int argc,char*argv[]) {

	FILE *f;
	int i = 0, j, k, n_t = 0, state = 0;
	char  buf[25];
	st temp[25];
	char ter[25] = { 0 };
	int ter_idx = 0;
	char tmp;
	char reduce_ch;
	int temp1, table_idx = 0, mark_idx = 0;
	int stack_tmp1, stack_tmp2, state_tmp, buf_tmp[25];
	int idx_tmp, line_count = 0;
	char inputbuf[25] = { 0 };
	stack_int s;
	count = 0;

	stackinit_int(&s);
	f = fopen(argv[1], "r");
	//if (fopen_s(&f, "rule.txt", "r"))
	if (f == NULL) {
		printf("File can't open!\n");
		return -1;
	}
	while (!feof(f))
	{
		fgets(buf, sizeof(buf), f);
		i++;
		if (i % 2 == 0) {

				strcpy(production[count++], buf);  //read the rule and set the production rule
		}
	}
	for (i = 0; i < count-1; i++)
	{
		if (i < count - 1)
		{
			j = strlen(production[i]) - 2;
			production[i][j] = '\0';
		}
	}
	for (i = 0; i < count; i++)  // look for nonterminal of production rule 
	{
		for (k = 0; production[i][k] != '\0'; k++)
		{
			if (k == 1)
				continue;
			for (j = 0; j < n_t; j++)
			{
				if (production[i][k] == nonterminal[j])
					state = 1;
			}
			if (state != 1 && isupper(production[i][k]))
				nonterminal[n_t++] = production[i][k];
			state = 0;
			if (i == count - 1)
				nonterminal[n_t] = '\0';
		}
	}
	state = 0;
	for (i = 0; i < count; i++)
	{
		for (j = 0; j < strlen(production[i]); j++)
		{
			tmp = production[i][j];
			for (k = 0; k <= ter_idx; k++)
			{
				if (ter[k] == tmp)
					state = 1;
			}
			if (state == 0 && tmp != '>'&&tmp != '#')
				ter[ter_idx++] = tmp;
			state = 0;
		}
	}
	follow[0].in[0] = '$';
	for (i = 0; i < n_t; i++) {                           //intialize  first,follow
		find_first(first[i].in, nonterminal[i]);
		first[i].n_t = nonterminal[i];
		follow[i].n_t = nonterminal[i];
		follow[i].in[1] = '\0';
	}
	do {
		copyst(temp, follow);
		for (i = 0; i < n_t; i++) {
			find_follow(follow[i].in, nonterminal[i]);
		}

	} while (comparest(follow, temp)); //더이상 안변할때까지 follow반복해서 구함. 

	closureset();
	for (i = 0; i < strlen(ter); i++) 
	{
		if (ter[i] > 90 || ter[i] < 65)
		{
			table[0][table_idx++] = ter[i];
		}
	}
	table[0][table_idx++] = '$';   ////initialize the table
	for (i = 0; i < strlen(ter); i++)
	{
		if (ter[i] <= 90 && ter[i] >= 65){
			table[0][table_idx++] = ter[i];
		}
	}

	for (i = 0; i < col_idx; i++)   ////Construct the table
	{
		for (j = 0; j < ter_idx; j++)
		{
			if (gotopro(i, ter[j]) >= -1)
			{
				if (ter[j] <= 90 && ter[j] >= 65)
				{
					for (int k = 0; k <= strlen(ter); k++)
					{
						if (table[0][k] == (int)ter[j])
							temp1 = k;
					}
					table[i + 1][temp1] = gotopro(i, ter[j]);   // using gotopro() store the value in table
				}
				else{

					for (int k = 0; k <= strlen(ter); k++)
					{
						if (table[0][k] == (int)ter[j])
							temp1 = k;
					}
					table[i + 1][temp1] = gotopro(i, ter[j]) + SHIFT;  //IF shift 5 => store the table SHIFT+5==205
				}
			}
		}
		for (j = 0; strlen(canonical[i].set[j]) != 0; j++)
		{
			if ('.' == canonical[i].set[j][strlen(canonical[i].set[j]) - 1])
			{
				if (canonical[i].set[j][0] != AUGMENT)
					mark_idx = strlen(canonical[i].set[j]) - 1;
				else
				{
					for (int l = 0; l < strlen(ter); l++)
					{
						if (table[0][l] == '$')
							table[i + 1][l] = -1;

					}
				}
			}
			if (mark_idx != 0)
			{
				for (int l = 0; l < count; l++)
				{
					if (strncmp(production[l], canonical[i].set[j], mark_idx) == 0)
					{
						reduce_ch = production[l][0];
						for (int m = 0; m < strlen(nonterminal); m++)
						{
							if (follow[m].n_t == reduce_ch)
							{
								for (int n = 0; n < strlen(follow[m].in); n++)
								{
									for (int o = 0; o < strlen(ter); o++)
									{
										if (follow[m].in[n] == table[0][o])
										{
											table[i + 1][o] = l + REDUCE + 1; //IF reduce5 => store the table REDUCE+5==305
										}
									}
								}
							}
						}
					}
				}
			}
			mark_idx = 0;
		}

	}

	//input 시작
	printf(">> ");
	scanf("%s", inputbuf);
	//for (i = 0; i < strlen(inputbuf); i++)
	//{
	//if (inputbuf[i] == '\n')
	//inputbuf[i] == '\0';
	//}
	while (strcmp(inputbuf, "exit") != 0)
	{
		if (strcmp(inputbuf, "RULE") == 0)
		{
			for (i = 0; i < count; i++)  //print production rule
			{
				printf("[R%d] : ", i + 1);
				printf("%s\n", production[i]);
			}
		}
		else if (strcmp(inputbuf, "FIRST") == 0)
		{
			for (i = 0; i < n_t; i++) {  //print first
				printf("FIRST(%c) : %s\n", first[i].n_t, first[i].in);
			}
		}
		else if (strcmp(inputbuf, "FOLLOW") == 0)
		{
			for (i = 0; i < n_t; i++) {  //print follow
				printf("FOLLOW(%c) : %s\n", follow[i].n_t, follow[i].in);
			}
		}
		else if (strcmp(inputbuf, "TABLE") == 0)
		{
			for (i = 0; i < col_idx; i++){   //table 출력
				line_count = 0;
				for (j = 0; table[0][j] != 0; j++)
				{
					if (table[i + 1][j] != 0)
					{
						line_count++;
					}
				}
				if (line_count != 0)
				{
					printf("%d :", i);
					for (j = 0; table[0][j] != 0; j++)
					{
						if (table[i + 1][j] != 0)
						{
							if (table[i + 1][j] == -1){
								printf("%c[ACCEPT]", table[0][j]);

							}
							else if (table[i + 1][j] >= 300) //reduce=300 
							{
								printf("%c[r%d] ", table[0][j], table[i + 1][j] - REDUCE);
							}
							else if (table[i + 1][j] >= 200)//shift=200
							{
								printf("%c[s%d] ", table[0][j], table[i + 1][j] - SHIFT);
							}
							else
								printf("%c[%d] ", table[0][j], table[i + 1][j]);
						}
					}
					printf("\n");
				}

			}
		}
		else if (strcmp(inputbuf, "ACTION") == 0){

			for (int k = 0; table[0][k] != 0; k++)
			{
				if (table[0][k] == '$')
					idx_tmp = k;
			}
			for (i = 0; i < col_idx; i++){   //print ACTION table
				line_count = 0;
				for (j = 0; j <= idx_tmp; j++)
				{
					if (table[i + 1][j] != 0)
					{
						line_count++;
					}
				}
				if (line_count != 0)
				{
					printf("%d :", i);
					for (j = 0; j <= idx_tmp; j++)
					{
						if (table[i + 1][j] != 0)
						{
							if (table[i + 1][j] == -1){
								printf("%c[ACCEPT]", table[0][j]);

							}
							else if (table[i + 1][j] >= 300) //reduce=300
							{
								printf("%c[r%d] ", table[0][j], table[i + 1][j] - REDUCE);
							}
							else if (table[i + 1][j] >= 200)//shift=200
							{
								printf("%c[s%d] ", table[0][j], table[i + 1][j] - SHIFT);
							}
						}

					}
					printf("\n");
				}

			}
		}
		else if (strcmp(inputbuf, "GOTO") == 0){
			for (int k = 0; table[0][k] != 0; k++)
			{
				if (table[0][k] == '$')
					idx_tmp = k + 1;
			}
			for (i = 0; i < col_idx; i++){   //print GOTO table 
				line_count = 0;
				for (j = idx_tmp; table[0][j] != 0; j++)
				{
					if (table[i + 1][j] != 0)
					{
						line_count++;
					}
				}
				if (line_count != 0)
				{
					printf("%d :", i);
					for (j = idx_tmp; table[0][j] != 0; j++)
					{
						if (table[i + 1][j] != 0)
						{
							printf("%c[%d] ", table[0][j], table[i + 1][j]);
						}
					}
					printf("\n");
				}
			}
		}
		else if (strncmp(inputbuf, "I", 1) == 0){
			if (inputbuf[2] =='\0')
			{
				for (int i = 0; i < canonical[inputbuf[1] - 48].id; i++)
					printf("%s\n", canonical[inputbuf[1] - 48].set[i]);
			}
			else
			{
				for (int i = 0; i < canonical[10*(inputbuf[1]-48)+inputbuf[2] - 48].id; i++)
					printf("%s\t", canonical[10 * (inputbuf[1] - 48) + inputbuf[2] - 48].set[i]);
			}
			printf("\n");
		}
		else
		{
			inputbuf[strlen(inputbuf) + 1] = inputbuf[strlen(inputbuf) ];
			inputbuf[strlen(inputbuf)] = '$';

			stackinit_int(&s);
			push_int(0, &s);

			for (i = 0; i < strlen (inputbuf); i++){
				stack_tmp1 = pop_int(&s);
				push_int(stack_tmp1, &s);
				stack_tmp2 = inputbuf[i];
				for (j = 0; table[0][j] != 0; j++)
				{
					if (stack_tmp2 == table[0][j])
						temp1 = j;
				}

				if (table[stack_tmp1 + 1][temp1] >= REDUCE)
				{
					state_tmp = table[stack_tmp1 + 1][temp1] - REDUCE;
					if (strlen(production[state_tmp - 1]) == 3 && production[state_tmp - 1][strlen(production[state_tmp - 1]) - 1] == '#')
					{
						stack_tmp1=pop_int(&s);
						stack_tmp2= pop_int(&s);
						if (stack_tmp2 == '#')
						{
							stack_tmp1 = pop_int(&s);
							push_int(stack_tmp1, &s);
							push_int(production[state_tmp - 1][0], &s);
							push_int(gotopro(stack_tmp1, production[state_tmp - 1][0]), &s);
						}
						else{
							push_int(stack_tmp2, &s);
							push_int(stack_tmp1, &s);
							push_int('#', &s);
							push_int(stack_tmp1, &s);
						}
					}
					else{
						for (j = strlen(production[state_tmp - 1]) - 2; j > 0; j--)
						{
							pop_int(&s);
							pop_int(&s);
						}
						stack_tmp1 = pop_int(&s);
						push_int(stack_tmp1, &s);
						push_int(production[state_tmp - 1][0], &s);
						push_int(gotopro(stack_tmp1, production[state_tmp - 1][0]), &s);
					}
					i -= 1;
				}
				else if (table[stack_tmp1 + 1][temp1] >= SHIFT)
				{
					state_tmp = table[stack_tmp1 + 1][temp1] - SHIFT;
					push_int(stack_tmp2, &s);
					push_int(state_tmp, &s);

				}
				else if (table[stack_tmp1 + 1][temp1] == -1)
				{
					printf("ACCEPT\n");
					i = strlen(inputbuf) - 1;
				}
				else if (table[stack_tmp1 + 1][temp1] == 0)
				{
					printf("ERROR\n");
					i = strlen(inputbuf) - 1;

				}
			}

		}
		printf(">> ");
		scanf("%s", inputbuf);
		//for (i = 0; i < strlen(inputbuf); i++)
		//{
			//if (inputbuf[i] == '\n')
				//inputbuf[i] == '\0';
		//}
	}



	return 0;
}


