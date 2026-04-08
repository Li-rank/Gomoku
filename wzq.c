#include <string.h>
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h> //支持 uint64_t
#include <time.h>
#define SIZE 15
#define CHARSIZE 3
#define BOARD_WIDTH (SIZE + 2)                 // 一维棋盘（宽度加2，包含左右两边哨兵）
#define BOARD_AREA (BOARD_WIDTH * BOARD_WIDTH) // 总面积 17*17=289
#define WALL 3                                 // 哨兵值（边界=3）
#define MAX_MOVES_TO_CHECK 20                  // 限制每一层只搜索最可能的20步
// 棋型分级评分表
#define SCORE_FIVE 10000000     // 连五
#define SCORE_LIVE_FOUR 1000000 // 活四
#define SCORE_SLEEP_FOUR 100000 // 冲四
#define SCORE_LIVE_THREE 10000  // 活三
#define SCORE_SLEEP_THREE 1000  // 眠三
#define SCORE_LIVE_TWO 100      // 活二
#define SCORE_SLEEP_TWO 10      // 眠二
#define WIN_SCORE SCORE_FIVE    // 兼容旧名
void initRecordBorard(void);
void innerLayoutToDisplayArray(void);
void displayBoard(void);
void playerMove(int currentPlayer, int *lastRow, int *lastCol);
int checkWin(int row, int col);
void aiMove(int aiPlayer, int *row, int *col);
int isBan(int r, int c);
int comparePoints(const void *a, const void *b);
void makeMove(int idx, int player);
void unmakeMove(int idx, int player);
void updateScoreImpact(int idx, int mode);
int getLineShapeFast(int idx, int d, int player);
// 棋盘使用的是UTF-8编码，每一个中文字符占用3个字节。
// 空棋盘模板
char arrayForEmptyBoard[SIZE][SIZE * CHARSIZE + 1] =
    {
        "┏┯┯┯┯┯┯┯┯┯┯┯┯┯┓",
        "┠┼┼┼┼┼┼┼┼┼┼┼┼┼┨",
        "┠┼┼┼┼┼┼┼┼┼┼┼┼┼┨",
        "┠┼┼┼┼┼┼┼┼┼┼┼┼┼┨",
        "┠┼┼┼┼┼┼┼┼┼┼┼┼┼┨",
        "┠┼┼┼┼┼┼┼┼┼┼┼┼┼┨",
        "┠┼┼┼┼┼┼┼┼┼┼┼┼┼┨",
        "┠┼┼┼┼┼┼┼┼┼┼┼┼┼┨",
        "┠┼┼┼┼┼┼┼┼┼┼┼┼┼┨",
        "┠┼┼┼┼┼┼┼┼┼┼┼┼┼┨",
        "┠┼┼┼┼┼┼┼┼┼┼┼┼┼┨",
        "┠┼┼┼┼┼┼┼┼┼┼┼┼┼┨",
        "┠┼┼┼┼┼┼┼┼┼┼┼┼┼┨",
        "┠┼┼┼┼┼┼┼┼┼┼┼┼┼┨",
        "┗┷┷┷┷┷┷┷┷┷┷┷┷┷┛"};
// 此数组存储用于显示的棋盘
char arrayForDisplayBoard[SIZE][SIZE * CHARSIZE + 1];
char play1Pic[] = "●"; // 黑棋子（四个字节）
char play1CurrentPic[] = "▲";
char play2Pic[] = "◎"; // 白棋子
char play2CurrentPic[] = "△";
int lastRow = -1;
int lastCol = -1;
// IDDFS 时间控制
clock_t start_time;            // 搜索开始时间
int stopSearch = 0;            // 超时熔断标志 (已超时=1，停止搜索)
const double TIME_LIMIT = 15; // 限制 9.5秒
long long node_count = 0;      // 节点计数器，间歇检查时间
// 杀手启发表，存储一维索引idx
// MAX_DEPTH 设为 20 (配合 IDDFS)
int killerMoves[20][2];
// 历史启发记录表
// 记录每个格子在历史上引发剪枝的累积权重
int historyTable[BOARD_AREA];
// 缓存显示的提示信息
char messageBuffer[256] = "";
// 此数组用于记录当前的棋盘的格局
// 将二维数组替换为一维数组
int board[BOARD_AREA];
// 一维数组的4个方向偏移量：横向(+1), 纵向(+17), 右下(+18), 左下(+16);对应原棋盘中的：{0,1}, {1,0}, {1,1}, {1,-1}
int dirOffset[4] = {1, BOARD_WIDTH, BOARD_WIDTH + 1, BOARD_WIDTH - 1};
// 坐标转换：将二维坐标 (0~14) 转换为一维索引 (包含哨兵偏移+1)
#define IDX(r, c) ((r + 1) * BOARD_WIDTH + (c + 1))

// Zobrist哈希全局变量
// 随机数表记录棋盘状态
unsigned long long zobristTable[BOARD_AREA][2];
// 当前棋盘的哈希值
unsigned long long currentHash = 0;
#define TT_SIZE 0X3FFFFF
typedef struct
{
    unsigned long long key; // 校验码
    int depth;              // 搜索的深度
    int value;              // 记录分数
    int flag;               // 0:精确值, 1:下界(Alpha), 2:上界(Beta)
} TTEntry;

TTEntry tTable[TT_SIZE + 1];

// 生成随机数填充Zobrist表
void initZobrist()
{
    unsigned long long seed = 123456789;
    // 遍历整个一维数组
    for (int i = 0; i < BOARD_AREA; i++)
    {
        for (int k = 0; k < 2; k++)
        {
            seed ^= seed << 13;
            seed ^= seed >> 7;
            seed ^= seed << 17;
            zobristTable[i][k] = seed;
        }
    }
    memset(tTable, 0, sizeof(tTable));
}
// 存入哈希表
void recordHash(int depth, int val, int flag)
{
    int index = currentHash & TT_SIZE;
    tTable[index].key = currentHash;
    tTable[index].value = val;
    tTable[index].depth = depth;
    tTable[index].flag = flag;
}

// 查询哈希表
int probeHash(int depth, int alpha, int beta)
{
    int index = currentHash & TT_SIZE;
    TTEntry *entry = &tTable[index];
    // 校验码匹配
    if (entry->key == currentHash)
    {
        if (entry->depth >= depth)
        {
            if (entry->flag == 0)
                return entry->value;
            if (entry->flag == 1 && entry->value <= alpha)
                return alpha;
            if (entry->flag == 2 && entry->value >= beta)
                return beta;
        }
    }
    return -999999; // 未命中
}

int main()
{
#ifdef _WIN32
    system("chcp 65001 > nul");
#endif

    int mode = 0;
    int currentPlayer = 1; // 1:黑棋(先手), 2:白棋(后手)
    int aiPlayer = 0;

    lastRow = -1;
    lastCol = -1;

    printf("欢迎来到五子棋!  作者：李俊贤\n");
    printf("请选择模式 (0: 人人对战, 1: 人机对战): ");
    if (scanf("%d", &mode) != 1)
        mode = 0;

    initRecordBorard();

    if (mode == 1)
    {
        printf("请选择先手方 (执黑): \n");
        printf("  1. 玩家先手 (玩家执黑)\n");
        printf("  2. AI 先手 (AI 执黑)\n");
        printf("请输入选项: ");
        int choice;
        if (scanf("%d", &choice) != 1)
        {
            choice = 1;
            // 清空输入缓冲区
            int c;
            while ((c = getchar()) != '\n' && c != EOF)
                ;
        }

        if (choice == 2)
        {
            aiPlayer = 1; // AI执黑
            printf("设置完毕：AI 执黑 (●)，玩家 执白 (◎)\n");
        }
        else
        {
            aiPlayer = 2; // AI执白
            printf("设置完毕：玩家 执黑 (●)，AI 执白 (◎)\n");
        }
    }

    while (1)
    {
        innerLayoutToDisplayArray();
        displayBoard();

        // 谁的回合
        if (mode == 1 && currentPlayer == aiPlayer)
        {
            // AI 回合
            int r, c;
            printf("AI正在思考...\n");
            clock_t start = clock();
            aiMove(aiPlayer, &r, &c);
            clock_t end = clock();
            double time_spent = (double)(end - start) / CLOCKS_PER_SEC;
            int idx = IDX(r, c);
            makeMove(idx, aiPlayer);

            lastRow = r;
            lastCol = c;
            sprintf(messageBuffer, "AI落子: %c%d (耗时 %.2f秒)", 'A' + c, SIZE - r, time_spent);
        }
        else
        {
            // 人类回合
            playerMove(currentPlayer, &lastRow, &lastCol);
        }

        // 胜负判定
        if (checkWin(lastRow, lastCol) == 1)
        {
            innerLayoutToDisplayArray();
            displayBoard();
            printf("\n=============================\n");
            if (currentPlayer == 1)
                printf("    黑棋(●) 获胜！\n");
            else
                printf("    白棋(◎) 获胜！\n");
            printf("=============================\n");
            printf("\n游戏结束，按回车键退出...");
            // 清理输入缓冲区
            int c;
            while ((c = getchar()) != '\n' && c != EOF);
            // 等待用户按下回车
            getchar();
            break;
        }
        // 切换执棋方 (1变2, 2变1)
        currentPlayer = (currentPlayer == 1) ? 2 : 1;
    }
    return 0;
}

// 将arrayForInnerBoardLayout中记录的棋子位置，转化到arrayForDisplayBoard中
void innerLayoutToDisplayArray(void)
{
    int i, j;
    // 复制空棋盘背景
    for (i = 0; i < SIZE; i++)
    {
        strcpy(arrayForDisplayBoard[i], arrayForEmptyBoard[i]);
    }

    // 扫描逻辑棋盘，将棋子画上去
    for (i = 0; i < SIZE; i++)
    {
        for (j = 0; j < SIZE; j++)
        {
            // 使用 IDX(i, j) 获取一维索引
            int idx = IDX(i, j);

            if (board[idx] != 0)
            { // 只有非空才绘制
                int offset = j * CHARSIZE;
                char *picToUse = NULL;
                int isLastMove = (i == lastRow && j == lastCol);

                if (board[idx] == 1)
                {
                    picToUse = isLastMove ? play1CurrentPic : play1Pic;
                }
                else if (board[idx] == 2)
                {
                    picToUse = isLastMove ? play2CurrentPic : play2Pic;
                }

                if (picToUse != NULL)
                {
                    strncpy(&arrayForDisplayBoard[i][offset], picToUse, CHARSIZE);
                }
            }
        }
    }
}

// 显示棋盘格局
void displayBoard(void)
{
    int i;
    // 第一步：清屏
    #ifdef _WIN32
    system("cls"); // Windows 系统指令
    #else
    system("clear"); // Linux/Mac 系统指令
    #endif
    // 第二步：将arrayForDisplayBoard输出到屏幕上
    for (i = 0; i < SIZE; i++)
    {
        printf("%2d %s\n", SIZE - i, arrayForDisplayBoard[i]);
    }
    // 第三步：输出最下面的一行字母A B
    printf("   ");
    for (i = 0; i < SIZE; i++)
    {
        printf("%c ", 'A' + i);
    }
    printf("\n");
    if (strlen(messageBuffer) > 0)
    {
        printf("\n>> %s\n", messageBuffer);
    }
}

// 判断胜负函数，1表示获胜，0表示未分胜负
int checkWin(int r, int c)
{
    int idx = IDX(r, c);
    int color = board[idx];

    // 四个方向：横、竖、右下斜、左下斜（dirOffset 一维数组偏移量在全局定义）
    for (int i = 0; i < 4; i++)
    {
        int count = 1;
        int d = dirOffset[i];

        // 向正方向扫描
        // 检测到WALL=3（边界）自动停止
        for (int k = 1; k < 5; k++)
        {
            if (board[idx + d * k] == color)
                count++;
            else
                break;
        }

        // 向反方向扫描
        for (int k = 1; k < 5; k++)
        {
            if (board[idx - d * k] == color)
                count++;
            else
                break;
        }

        if (color == 1)
        { // 黑棋长连判定
            if (count == 5)
                return 1;
        }
        else
        { // 白棋 >=5 获胜
            if (count >= 5)
                return 1;
        }
    }
    return 0;
}
// AI 核心
typedef struct
{
    int r, c;
    int score;
} Point;
// 检查坐标是否在棋盘内
int isValid(int r, int c)
{
    return (r >= 0 && r < SIZE && c >= 0 && c < SIZE);
}

// 1. 单线估值函数(支持跳活/跳冲/隔子杀)
// 计算 (r, c) 点在特定方向 (dr, dc) 上的棋型分数
int getLineScore(int idx, int d, int player)
{
    // 提取9格长度切片，current在 line[4]
    int line[9];
    for (int i = -4; i <= 4; i++)
    {
        line[i + 4] = board[idx + d * i];
    }
    // 情况1: 紧邻队友
    // line[3] 是 idx 左边一格
    if (line[3] == player)
        return 0;

    // 情况2: 隔子队友处理跳连
    // 如果左边是空，但再左边是队友，说明这是跳连
    if (line[3] == 0 && line[2] == player)
        return 0;

    // 第一层逻辑：绝对连五判断
    // 滑动窗口查5连
    for (int i = 0; i <= 4; i++)
    {
        int cnt = 0;
        for (int k = 0; k < 5; k++)
        {
            if (line[i + k] == player)
                cnt++;
            else
                break;
        }
        if (cnt == 5)
            return SCORE_FIVE;
    }

    // 第二层逻辑：其他关键模式匹配 (处理跳棋)
    // 检查 "纯连" 和 "空连"

    // 临时变量记录最高分
    int currentBest = 0;

// 辅助宏：检查边界是否越界或被堵 (WALL或对手)
#define IS_BLOCKED(idx) ((idx) < 0 || (idx) > 8 || line[(idx)] != 0)

    // 检查以中心为核心的棋型，强制包含当前落子点
    // 向左和向右延伸，统计连子数
    int countStrict = 1;
    int lStrict = 3, rStrict = 5;
    while (lStrict >= 0 && line[lStrict] == player)
    {
        countStrict++;
        lStrict--;
    }
    while (rStrict <= 8 && line[rStrict] == player)
    {
        countStrict++;
        rStrict++;
    }

    // 严格相连的评分
    int leftBlocked = IS_BLOCKED(lStrict);
    int rightBlocked = IS_BLOCKED(rStrict);

    if (countStrict == 4)
    {
        if (!leftBlocked && !rightBlocked)
            currentBest = (currentBest < SCORE_LIVE_FOUR) ? SCORE_LIVE_FOUR : currentBest;
        else
            currentBest = (currentBest < SCORE_SLEEP_FOUR) ? SCORE_SLEEP_FOUR : currentBest;
    }
    else if (countStrict == 3)
    {
        if (!leftBlocked && !rightBlocked)
            currentBest = (currentBest < SCORE_LIVE_THREE) ? SCORE_LIVE_THREE : currentBest;
        else
            currentBest = (currentBest < SCORE_SLEEP_THREE) ? SCORE_SLEEP_THREE : currentBest;
    }
    else if (countStrict == 2)
    {
        if (!leftBlocked && !rightBlocked)
            currentBest = (currentBest < SCORE_LIVE_TWO) ? SCORE_LIVE_TWO : currentBest;
        else
            currentBest = (currentBest < SCORE_SLEEP_TWO) ? SCORE_SLEEP_TWO : currentBest;
    }
    // 处理跳跃棋型
    // 用穷举法扫描以中心为起点的特定跳跃模式。
    // 目标：寻找 Jump Four (10111 结构) ：冲四；Jump Three (010110 结构) ：活三
    // 1. 找冲四 (4子1空): 11011, 10111, 11101

    for (int s = 0; s <= 4; s++)
    { // 窗口起点
        if (s > 4 || s + 4 < 4)
            continue; // 包含中心
        int c = 0, e = 0;
        for (int k = 0; k < 5; k++)
        {
            if (line[s + k] == player)
                c++;
            else if (line[s + k] == 0)
                e++;
            else
            {
                c = -1;
                break;
            } // 被堵
        }

        if (c == 4 && e == 1)
        {
            // 找到了 10111, 11011 等
            // 无论两头如何，至少是冲四
            currentBest = (currentBest < SCORE_SLEEP_FOUR) ? SCORE_SLEEP_FOUR : currentBest;
        }
    }

    // 2. 找跳活三和眠三 (3子1空，且两头空): 010110, 011010
    // 中间4格呈现 "3子1空" ( 1011, 1101)
    // 如果两头空->活三；如果只有一头空->眠三

    for (int s = 0; s <= 3; s++) // 窗口起点，窗口跨度
    {
        // 1. 快速检查：包含中心点 idx=4
        if (s > 4 || s + 5 < 4)
            continue;

        // 2. 检查两端边界情况
        // leftEnd, rightEnd: 0表示空位，1表示有子/越界
        int leftEnd = line[s];
        int rightEnd = line[s + 5];

        // 如果两头都被堵死，则不可能是活三或常规眠三，跳过
        if (leftEnd != 0 && rightEnd != 0)
            continue;

        // 3. 检查中间核心区域 (s+1 到 s+4)
        int c = 0, e = 0;
        for (int k = 1; k <= 4; k++)
        {
            if (line[s + k] == player)
                c++;
            else if (line[s + k] == 0)
                e++;
            else
            {
                c = -1; // 中间混入了对手的子，破坏结构
                break;
            }
        }

        // 4. 判定分数
        if (c == 3 && e == 1)
        {
            if (leftEnd == 0 && rightEnd == 0)
            {
                // 两头空 -> 活三 (0 1011 0)
                currentBest = (currentBest < SCORE_LIVE_THREE) ? SCORE_LIVE_THREE : currentBest;
            }
            else
            {
                // 只有一头空 -> 眠三 (2 1011 0)
                currentBest = (currentBest < SCORE_SLEEP_THREE) ? SCORE_SLEEP_THREE : currentBest;
            }
        }
    }

    // 4. 处理特殊的 10101 (双跳三)
    // 这是一个特殊的眠三，威胁略低于跳活三，但高于眠二
    // 如果窗口5内是 3子2空 (10101)，且无阻挡
    for (int s = 0; s <= 4; s++)
    {
        if (s > 4 || s + 4 < 4)
            continue;
        int c = 0, e = 0;
        for (int k = 0; k < 5; k++)
        {
            if (line[s + k] == player)
                c++;
            else if (line[s + k] == 0)
                e++;
            else
            {
                c = -1;
                break;
            }
        }
        if (c == 3 && e == 2)
        {
            currentBest = (currentBest < SCORE_SLEEP_THREE) ? SCORE_SLEEP_THREE : currentBest;
        }
    }

    return currentBest;
}

// 核心全盘扫描函数：线性扫描
void scanVector(int startIdx, int delta, int len, long long *bScore, long long *wScore)
{
    int pos = 0;
    while (pos < len)
    {
        int idx = startIdx + pos * delta;
        int val = board[idx];

        // 跳过空位和墙
        if (val == 0 || val == 3)
        {
            pos++;
            continue;
        }

        int color = val;
        int k = 1;
        // 1. 连续段长度
        while (pos + k < len && board[startIdx + (pos + k) * delta] == color)
        {
            k++;
        }

        // 2. 两端开口检查
        int leftOpen = 0;
        int rightOpen = 0;
        if (pos > 0 && board[startIdx + (pos - 1) * delta] == 0)
            leftOpen = 1;
        if (pos + k < len && board[startIdx + (pos + k) * delta] == 0)
            rightOpen = 1;

        int shapeLvl = 0;
        int jumpUsed = 0;

        // 3. 跳跃检测 (例如 1101)
        if (pos + k + 1 < len && board[startIdx + (pos + k) * delta] == 0 && board[startIdx + (pos + k + 1) * delta] == color)
        {
            int m = 2;
            int extraK = 1;
            while (pos + k + m < len && board[startIdx + (pos + k + m) * delta] == color)
            {
                extraK++;
                m++;
            }

            // 合并计算
            k += extraK;
            if (pos + k + 1 < len && board[startIdx + (pos + k + 1 - extraK + m) * delta] == 0)
                rightOpen = 1;
            // 只看跳后的最右边是不是空
            int endPosReal = pos + k - extraK + m; // 实际结束位置
            rightOpen = 0;                         // 重置
            if (startIdx + (endPosReal)*delta < BOARD_AREA && board[startIdx + (endPosReal)*delta] == 0)
                rightOpen = 1;

            jumpUsed = 1;
            // 中间的空位和后半段，避免重复算；pos+=k 只是跳过了棋子数，没跳过空位，需要额外跳过空位 (1格)。
            pos += 1;
        }

        // 4. 评分逻辑
        if (k >= 6)
            shapeLvl = 7;
        else if (k == 5)
            shapeLvl = 6;
        else if (k == 4)
        {
            if (jumpUsed)
                shapeLvl = 4; // 跳冲四
            else
            {
                if (leftOpen && rightOpen)
                    shapeLvl = 5;
                else if (leftOpen || rightOpen)
                    shapeLvl = 4;
            }
        }
        else if (k == 3)
        {
            if (jumpUsed)
            {
                if (leftOpen && rightOpen)
                    shapeLvl = 3; // 跳活三
                else if (leftOpen || rightOpen)
                    shapeLvl = 2;
            }
            else
            {
                if (leftOpen && rightOpen)
                    shapeLvl = 3;
                else if (leftOpen || rightOpen)
                    shapeLvl = 2;
            }
        }
        else if (k == 2)
        {
            if (leftOpen && rightOpen && !jumpUsed)
                shapeLvl = 1;
        }
        long long currentScore = 0;
        switch (shapeLvl)
        {
        case 7:
            if (color == 1)
                currentScore = -SCORE_FIVE; // 黑棋长连判负
            else
                currentScore = SCORE_FIVE; // 白棋长连判胜
            break;
        case 6:
            currentScore = SCORE_FIVE;
            break;
        case 5:
            currentScore = SCORE_LIVE_FOUR;
            break;
        case 4:
            currentScore = SCORE_SLEEP_FOUR;
            break;
        case 3:
            currentScore = SCORE_LIVE_THREE;
            break;
        case 2:
            currentScore = SCORE_SLEEP_THREE;
            break;
        case 1:
            currentScore = SCORE_LIVE_TWO;
            break;
        default:
            currentScore = 0;
        }

        if (color == 1)
            *bScore += currentScore;
        else
            *wScore += currentScore;

        pos += k;
    }
}

// 全盘扫描入口
int evaluateWholeBoard(int aiPlayer)
{
    long long bScore = 0;
    long long wScore = 0;

    // 横向
    for (int r = 0; r < SIZE; r++)
        scanVector(IDX(r, 0), 1, SIZE, &bScore, &wScore);
    // 纵向
    for (int c = 0; c < SIZE; c++)
        scanVector(IDX(0, c), BOARD_WIDTH, SIZE, &bScore, &wScore);
    // 主对角线
    for (int c = 0; c < SIZE; c++)
        scanVector(IDX(0, c), BOARD_WIDTH + 1, SIZE - c, &bScore, &wScore);
    for (int r = 1; r < SIZE; r++)
        scanVector(IDX(r, 0), BOARD_WIDTH + 1, SIZE - r, &bScore, &wScore);
    // 副对角线
    for (int c = 0; c < SIZE; c++)
        scanVector(IDX(0, c), BOARD_WIDTH - 1, c + 1, &bScore, &wScore);
    for (int r = 1; r < SIZE; r++)
        scanVector(IDX(r, SIZE - 1), BOARD_WIDTH - 1, SIZE - r, &bScore, &wScore);

    if (aiPlayer == 1)
        return (int)(bScore - wScore);
    else
        return (int)(wScore - bScore);
}
// 统一落子函数 (封装了 棋盘、哈希、分数更新)
void makeMove(int idx, int player)
{
    // 执行落子与哈希更新
    board[idx] = player;
    currentHash ^= zobristTable[idx][player - 1];
}

// 统一撤销函数
void unmakeMove(int idx, int player)
{
    // 执行撤销与哈希恢复
    board[idx] = 0;
    currentHash ^= zobristTable[idx][player - 1];
}
// 初始化函数 (重置全局分数)
void initRecordBorard(void)
{
    int i;
    for (i = 0; i < BOARD_AREA; i++)
    {
        board[i] = WALL;
    }
    for (int r = 0; r < SIZE; r++)
    {
        for (int c = 0; c < SIZE; c++)
        {
            board[IDX(r, c)] = 0;
        }
    }
    initZobrist();
    currentHash = 0;
}
// 按分数从高到低排序
int comparePoints(const void *a, const void *b)
{
    Point *p1 = (Point *)a;
    Point *p2 = (Point *)b;
    return p2->score - p1->score; // 降序
}

// 禁手判断模块
int isBan(int r, int c)
{
    int idx = IDX(r, c);
    // 只有空位能落子
    if (board[idx] != 0)
        return 0;

    // 1. 模拟落子
    board[idx] = 1;

    int fiveCount = 0;     // 连五个数
    int fourCount = 0;     // 四的个数 (活四+冲四)
    int threeCount = 0;    // 活三个数
    int overlineCount = 0; // 长连个数

    // 2. 扫描四个方向
    for (int k = 0; k < 4; k++)
    {
        // 直接调用getLineShapeFast函数，获取 Level (0-7)
        int lvl = getLineShapeFast(idx, dirOffset[k], 1); // 1代表黑棋

        if (lvl == 7)
            overlineCount++; // Level 7: 长连
        else if (lvl == 6)
            fiveCount++; // Level 6: 连五
        else if (lvl == 5)
            fourCount++; // Level 5: 活四
        else if (lvl == 4)
            fourCount++; // Level 4: 冲四 (四四禁手包含冲四)
        else if (lvl == 3)
            threeCount++; // Level 3: 活三
    }

    // 3. 恢复棋盘
    board[idx] = 0;

    // 4. 判定逻辑 (优先级：五 > 长连 > 四四 > 三三)
    // 如果成五，无论有多少禁手，都算赢
    if (fiveCount > 0)
        return 0;

    // 长连禁手
    if (overlineCount > 0)
        return 1;

    // 四四禁手 (包括：双冲四、双活四、冲四+活四)
    if (fourCount >= 2)
        return 1;

    // 三三禁手
    if (threeCount >= 2)
        return 1;

    return 0; // 合法
}

// 邻居判断
int hasNeighbor(int idx)
{
    // 反解出二维坐标
    int r = (idx / BOARD_WIDTH) - 1;
    int c = (idx % BOARD_WIDTH) - 1;

    for (int i = -2; i <= 2; i++)
    {
        for (int j = -2; j <= 2; j++)
        {
            if (i == 0 && j == 0)
                continue;

            // 计算邻居的真实坐标
            int nr = r + i;
            int nc = c + j;

            // 检查坐标是否在棋盘范围内
            if (nr >= 0 && nr < SIZE && nc >= 0 && nc < SIZE)
            {
                int nIdx = IDX(nr, nc);
                // 只关心是否有棋子 (1=黑, 2=白)
                if (board[nIdx] == 1 || board[nIdx] == 2)
                    return 1;
            }
        }
    }
    return 0;
}
// 单线估值函数
// 返回值定义：
// 0: 无威胁
// 1: 活二 (Level 1)
// 2: 眠三 (Level 2)
// 3: 活三 (Level 3)
// 4: 冲四 (Level 4)
// 5: 活四 (Level 5)
// 6: 连五 (Level 6)
// 7: 长连 (Level 7)
int getLineShapeFast(int idx, int d, int player)
{
    // 基础数据
    int totalStones = 1; // 包含当前落子
    int openEnds = 0;    // 两端开放情况
    int gapUsed = 0;     // 是否使用过跳跃

    // 向正方向扫描
    int side1Gap = 0;
    int k = 1;
    for (; k <= 4; k++)
    {
        int val = board[idx + d * k];
        if (val == player)
        {
            totalStones++;
        }
        else if (val == 0)
        {
            // 遇到空位，尝试跳跃
            // 只有当这是第一次遇到空位，且空位后面紧接着己方棋子时，才允许跳跃
            if (side1Gap == 0 && board[idx + d * (k + 1)] == player)
            {
                side1Gap = 1; // 标记已跳跃
            }
            else
            {
                openEnds++;
                break; // 停止扫描 (真正的端点)
            }
        }
        else
        {
            break; // 遇到墙或对手，停止
        }
    }

    // 向反方向扫描
    int side2Gap = 0;
    k = 1;
    for (; k <= 4; k++)
    {
        int val = board[idx - d * k];
        if (val == player)
        {
            totalStones++;
        }
        else if (val == 0)
        {
            if (side2Gap == 0 && board[idx - d * (k + 1)] == player)
            {
                side2Gap = 1;
            }
            else
            {
                openEnds++;
                break;
            }
        }
        else
        {
            break;
        }
    }

    // 汇总跳跃情况
    gapUsed = side1Gap + side2Gap;

    // 评级判定

    // 1. 长连与连五 (最高优先级)
    if (totalStones >= 6)
        return 7; // 长连
    if (totalStones == 5)
    {
        if (gapUsed > 0)
            return 4; // 有空位的5子(110111)是冲四(或假四)，不是连五
        else
            return 6; // 真正的连五
    }

    // 2. 四子情况
    if (totalStones == 4)
    {
        // 只要有跳跃，必然是冲四
        if (gapUsed > 0)
            return 4; // 冲四 (Level 4)

        // 连续四子：看两头
        if (openEnds == 2)
            return 5; // 活四 (Level 5)
        if (openEnds == 1)
            return 4; // 冲四 (Level 4)
        return 0;     // 死四
    }

    // 3. 三子情况
    if (totalStones == 3)
    {
        // 特例：1 0 1 0 1 (双跳三)，结构松散，降级为眠三
        if (gapUsed > 1)
            return 2;
        // 活三判据：两头空
        // 包含：0 1 1 1 0 (连续), 0 1 0 1 1 0 (跳活三)
        if (openEnds == 2)
            return 3; // 活三 (Level 3)
        if (openEnds == 1)
            return 2; // 眠三 (Level 2)
        return 0;
    }

    // 4. 二子情况
    if (totalStones == 2)
    {
        if (openEnds == 2)
            return 1; // 活二
        return 0;
    }

    return 0;
}
// 极速估值函数
// 核心逻辑：只看形状，不问规则。规则由 Search 层的 isBan 过滤。
int evaluateMoveStrengthFast(int idx, int aiPlayer)
{
    int humanPlayer = (aiPlayer == 1) ? 2 : 1;
    long long score = 0;

    // [0]:无, [1]:活二, [2]:眠三, [3]:活三, [4]:冲四, [5]:活四, [6]:连五, [7]:长连
    int myShapes[8] = {0};
    int oppShapes[8] = {0};

    // 1. 进攻评估 (我方)
    for (int i = 0; i < 4; i++)
    {
        int d = dirOffset[i];
        int lvl = getLineShapeFast(idx, d, aiPlayer);
        myShapes[lvl]++;
    }

    // 2. 进攻打分
    // 自我禁手简单过滤 (只通过形状数量判断，不调用耗时函数)
    // 真正的禁手过滤由 isBan 负责，这里只需模糊判断
    int isBanShape = 0;
    if (aiPlayer == 1)
    {
        if (myShapes[7] > 0)
            isBanShape = 1;
        if ((myShapes[5] + myShapes[4]) >= 2)
            isBanShape = 1;
        if (myShapes[3] >= 2)
            isBanShape = 1;
        if (myShapes[6] > 0)
            isBanShape = 0; // 成五解禁
    }
    // 看起来像禁手，大幅降低分数，但不直接返回0，
    // 基于形状的猜测，没有 isBan 准确。让搜索去验证。
    if (isBanShape)
        score -= 1000000;

    // TIER 1: 直接胜利
    if (myShapes[6] > 0)
        return SCORE_FIVE * 10;

    // TIER 2: 必胜 (我方活四)
    if (myShapes[5] > 0)
        return SCORE_FIVE * 9;

    // 3. 防守评估 (对方)
    for (int i = 0; i < 4; i++)
    {
        int lvl = getLineShapeFast(idx, dirOffset[i], humanPlayer);
        oppShapes[lvl]++;
    }

    // 对方禁手简单判断
    int isOppBan = 0;
    if (humanPlayer == 1)
    {
        if (oppShapes[7] > 0)
            isOppBan = 1;
        if ((oppShapes[5] + oppShapes[4]) >= 2)
            isOppBan = 1;
        if (oppShapes[3] >= 2)
            isOppBan = 1;
        if (oppShapes[6] > 0)
            isOppBan = 0;
    }

    // 如果不是对方的禁手，或者能成五，必须防守
    if (!isOppBan || oppShapes[6] > 0)
    {
        // 阻挡对手胜利

        // 阻挡连五 (9500万)
        if (oppShapes[6] > 0)
            return SCORE_FIVE * 9 + SCORE_FIVE / 2;

        // 阻挡活四 (8000万)
        if (oppShapes[5] > 0)
            return SCORE_FIVE * 8;

        // 阻挡冲四 (5000万)
        if (oppShapes[4] > 0)
            score += SCORE_FIVE * 5;

        // 阻挡活三 (2000万)
        if (oppShapes[3] > 0)
            score += SCORE_FIVE * 2;

        // 预防性防守 (阻挡对手双杀)
        if ((oppShapes[5] + oppShapes[4]) >= 2)
            score += SCORE_FIVE + SCORE_FIVE / 2;
        if (oppShapes[4] >= 1 && oppShapes[3] >= 1)
            score += SCORE_FIVE + SCORE_FIVE / 2;
        if (oppShapes[3] >= 2)
            score += SCORE_FIVE;
    }

    // 4. 继续进攻打分
    // 战术进攻

    // 制造双杀 (500万)
    if (aiPlayer == 1)
    {
        if (myShapes[4] >= 1 && myShapes[3] >= 1)
            score += SCORE_LIVE_FOUR * 5;
    }
    else
    {
        if ((myShapes[5] + myShapes[4]) >= 2)
            score += SCORE_LIVE_FOUR * 5;
        if (myShapes[4] >= 1 && myShapes[3] >= 1)
            score += SCORE_LIVE_FOUR * 5;
        if (myShapes[3] >= 2)
            score += SCORE_LIVE_FOUR * 3;
    }

    // 基础形状分 (叠加)
    if (myShapes[4] > 0)
        score += SCORE_SLEEP_FOUR * 4;
    if (myShapes[3] > 0)
        score += SCORE_LIVE_THREE * 10;
    if (myShapes[2] > 0)
        score += SCORE_SLEEP_THREE;
    if (myShapes[1] > 0)
        score += SCORE_LIVE_TWO;

    // 位置分
    int r = (idx / BOARD_WIDTH) - 1;
    int c = (idx % BOARD_WIDTH) - 1;
    score -= abs(r - 7) + abs(c - 7);

    return (int)score;
}
// 着法生成
int generateMoves(Point moves[], int player, int depth)
{
    int count = 0;
    for (int r = 0; r < SIZE; r++)
    {
        for (int c = 0; c < SIZE; c++)
        {
            int idx = IDX(r, c);
            if (board[idx] == 0)
            {
                // 只搜索有邻居的点
                if (hasNeighbor(idx) || (idx == IDX(7, 7)))
                {
                    if (player == 1 && isBan(r, c))
                    {
                        continue;
                    }
                    // 快速估值
                    int score = evaluateMoveStrengthFast(idx, player);

                    // 杀手启发
                    if (depth >= 0 && depth < 20)
                    {
                        if (idx == killerMoves[depth][0])
                            score += 10000000; // 提权
                        else if (idx == killerMoves[depth][1])
                            score += 5000000;
                    }

                    // 历史启发
                    score += historyTable[idx];

                    // 阈值筛选
                    if (score > -200)
                    {
                        moves[count].r = r;
                        moves[count].c = c;
                        moves[count].score = score;
                        count++;
                    }
                }
            }
        }
    }
    qsort(moves, count, sizeof(Point), comparePoints);
    if (count > MAX_MOVES_TO_CHECK)
        count = MAX_MOVES_TO_CHECK;
    return count;
}

// 玩家落子
void playerMove(int currentPlayer, int *lastRow, int *lastCol)
{
    int rowInput;
    char colInput;
    int isValidMove = 0;

    while (isValidMove == 0)
    {
        if (currentPlayer == 1)
            printf("请黑棋(●)落子: ");
        else
            printf("请白棋(◎)落子: ");

        if (scanf(" %c%d", &colInput, &rowInput) != 2)
        {
            printf("格式错误!\n");
            int c;
            while ((c = getchar()) != '\n' && c != EOF)
                ;
            continue;
        }
        int r = SIZE - rowInput;
        int c = (colInput >= 'a') ? (colInput - 'a') : (colInput - 'A');

        // 越界检查
        if (r < 0 || r >= SIZE || c < 0 || c >= SIZE)
        {
            printf("坐标越界！\n");
            continue;
        }

        int idx = IDX(r, c);
        if (board[idx] != 0)
        {
            printf("此处已有棋子！\n");
            continue;
        }
        if (currentPlayer == 1 && isBan(r, c))
        {
            printf("【禁手】黑棋不能下这里！\n");
            continue;
        }

        // 落子
        makeMove(idx, currentPlayer);
        *lastRow = r;
        *lastCol = c;
        isValidMove = 1;
    }
}

// Minimax 递归函数 (Alpha-Beta 剪枝 + PVS + 熔断)
int minimax(int depth, int alpha, int beta, int isMax, int aiPlayer)
{
    // 1. 间歇性检查时间 (每2048个节点检查一次)
    node_count++;
    if ((node_count & 2047) == 0)
    {
        if (!stopSearch)
        { // 如果还没停，才去查系统时间
            double spent = (double)(clock() - start_time) / CLOCKS_PER_SEC;
            if (spent >= TIME_LIMIT)
            {
                stopSearch = 1; // 熔断
            }
        }
    }
    // 如果已熔断，立即返回无效值
    if (stopSearch)
        return 0;
    int val = probeHash(depth, alpha, beta);
    if (val != -999999)
        return val;

    int score = evaluateWholeBoard(aiPlayer);
    // 深度耗尽或分出胜负
    if (depth <= 0 || score >= WIN_SCORE / 2 || score <= -WIN_SCORE / 2)
    {
        return score;
    }

    Point moves[SIZE * SIZE];
    int humanPlayer = (aiPlayer == 1) ? 2 : 1;
    int actingPlayer = isMax ? aiPlayer : humanPlayer;

    int moveCount = generateMoves(moves, actingPlayer, depth);
    if (moveCount == 0)
        return 0;

    int bestVal = isMax ? -2000000000 : 2000000000;
    int flag = 1;

    for (int i = 0; i < moveCount; i++)
    {
        int r = moves[i].r;
        int c = moves[i].c;
        int idx = IDX(r, c);

        makeMove(idx, actingPlayer);

        // 递归
        int v;
        if (i == 0)
        {
            // 1. 主要变例搜索 (PVS)：全力搜索排序后的第一个节点
            v = minimax(depth - 1, alpha, beta, !isMax, aiPlayer);
        }
        else
        {
            // 假设后续节点都不如第一个好，验证这个假设
            if (isMax)
            {
                // Max 节点：证明 v <= alpha
                // 窗口设为 (alpha, alpha+1)
                v = minimax(depth - 1, alpha, alpha + 1, !isMax, aiPlayer);

                if (v > alpha && v < beta)
                {
                    // 假设失败，比 alpha 还要大，重新用全窗口精确搜索
                    v = minimax(depth - 1, alpha, beta, !isMax, aiPlayer);
                }
            }
            else
            {
                // Min 节点：证明 v >= beta
                // 窗口设为 (beta-1, beta)
                v = minimax(depth - 1, beta - 1, beta, !isMax, aiPlayer);

                if (v < beta && v > alpha)
                {
                    // 假设失败，比 beta 还要小（对Min更好），重新搜索
                    v = minimax(depth - 1, alpha, beta, !isMax, aiPlayer);
                }
            }
        }
        unmakeMove(idx, actingPlayer);

        // 2. 递归回来后，立刻检查是否触发熔断
        if (stopSearch)
            return 0; // 这一次结果无效，直接向上层返回

        if (isMax)
        {
            if (v > bestVal)
                bestVal = v;
            if (bestVal > alpha)
            {
                alpha = bestVal;
                flag = 0;
            }
            if (beta <= alpha)
            {
                // Beta 剪枝时记录杀手步
                if (depth >= 0 && depth < 20)
                {
                    // 如果不是已经记录的主杀手，则进行替换
                    if (killerMoves[depth][0] != idx)
                    {
                        killerMoves[depth][1] = killerMoves[depth][0]; // 原主杀手降级为副杀手
                        killerMoves[depth][0] = idx;                   // 当前步升级为主杀手
                    }
                }
                flag = 2;
                break; // Beta Cutoff
            }
        }
        else
        {
            if (v < bestVal)
                bestVal = v;
            if (bestVal < beta)
            {
                beta = bestVal;
                flag = 0;
            }
            if (beta <= alpha)
            {
                // Alpha 剪枝 (对于Min节点)
                if (depth >= 0 && depth < 20)
                {
                    if (killerMoves[depth][0] != idx)
                    {
                        killerMoves[depth][1] = killerMoves[depth][0];
                        killerMoves[depth][0] = idx;
                    }
                }
                flag = 1;
                break; // Alpha Cutoff
            }
        }
    }

    // 3. 只有未超时的完整结果才写入哈希表
    if (!stopSearch)
    {
        recordHash(depth, bestVal, flag);
    }

    return bestVal;
}

// aiMove 入口 (IDDFS 迭代加深)
void aiMove(int aiPlayer, int *row, int *col)
{
    Point moves[SIZE * SIZE];

    // 1. 生成初始候选步 (只生成一次)
    int moveCount = generateMoves(moves, aiPlayer, 20);

    // 开局第一手
    if (moveCount == 0 || (moveCount == 1 && board[IDX(7, 7)] == 0))
    {
        *row = 7;
        *col = 7;
        return;
    }

    // 初始化全局时间控制
    start_time = clock();
    stopSearch = 0;
    node_count = 0;
    // 清空杀手表，防止上一轮干扰
    memset(killerMoves, 0, sizeof(killerMoves));
    // 清空历史表
    memset(historyTable, 0, sizeof(historyTable));

    int bestR = -1, bestC = -1;
    int globalBestVal = -2000000000;

    // 2. 迭代加深循环
    // 从 2 层开始，每次加 2 层 (2, 4, 6, 8, 10...)
    // 设定一个上限20层
    for (int depth = 2; depth <= 20; depth += 2)
    {

        // 根节点排序优化
        // 如果上一层找到了一个 bestR/bestC，那么这一层第一个搜
        // 冒泡排序
        if (bestR != -1)
        {
            for (int i = 0; i < moveCount; i++)
            {
                if (moves[i].r == bestR && moves[i].c == bestC)
                {
                    // 交换到第一个
                    Point temp = moves[0];
                    moves[0] = moves[i];
                    moves[i] = temp;
                    break;
                }
            }
        }
        int currentDepthBestVal = -2000000000;
        int currentDepthBestR = -1;
        int currentDepthBestC = -1;

        // 对每一个候选步进行搜索
        for (int i = 0; i < moveCount; i++)
        {
            int r = moves[i].r;
            int c = moves[i].c;
            int idx = IDX(r, c);

            makeMove(idx, aiPlayer);

            // 搜索窗口：全窗口
            int val = minimax(depth - 1, -2000000000, 2000000000, 0, aiPlayer);

            unmakeMove(idx, aiPlayer);

            // 检查熔断
            if (stopSearch)
            {
                break; // 跳出 moveCount 循环
            }

            // 更新本层最佳
            if (val > currentDepthBestVal)
            {
                currentDepthBestVal = val;
                currentDepthBestR = r;
                currentDepthBestC = c;
            }
        }

        // 3. 只有当这一层搜完且没超时，才更新全局最佳
        if (!stopSearch)
        {
            bestR = currentDepthBestR;
            bestC = currentDepthBestC;
            globalBestVal = currentDepthBestVal;

            double spent = (double)(clock() - start_time) / CLOCKS_PER_SEC;
            printf("IDDFS: Depth %d completed in %.2fs. Best: %c%d Score: %d\n",
                   depth, spent, 'A' + bestC, SIZE - bestR, globalBestVal);

            // 如果已经算出了必胜分 (连五)，不需要再搜更深
            if (globalBestVal >= WIN_SCORE - 100) // 减去深度的折损
            {
                printf("IDDFS: 必胜\n");
                break;
            }
        }
        else
        {
            printf("IDDFS: Depth %d 超时 (%.2fs)! 丢弃本层结果，使用 Depth %d 的最佳着法。\n",
                   depth, (double)(clock() - start_time) / CLOCKS_PER_SEC, depth - 2);
            break; // 退出 depth 循环
        }
    }

    *row = bestR;
    *col = bestC;
}