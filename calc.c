// Ege Engin 260ADM039
// Compile with: gcc -O2 -Wall -Wextra -std=c17 -o calc calc.c -lm
// Resources used: Lecture Slides on Files/Directories, Memory Allocation & CLI Arguments;
// C Standard Library Documentation (cppreference.com);
// C17 standard documentation, standard recursive descent parsing logic;
// StackOverFlow threads on right-associative operator parsing;
// GeeksforGeeks dynamic memory & file I/O in C;
//
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <ctype.h>
#include <math.h>
#include <errno.h>
#include <dirent.h>
#include <sys/stat.h>
#include <stdbool.h>

#define STUDENT_NAME "ege"
#define STUDENT_LASTNAME "engin"
#define STUDENT_ID "260ADM039"

/*
 * Section 8:
 *
 * 1. Tracking Positions: Positions were tracked using one based characters counter current_pos.
 *    Increments on every byte reads from input buffer and each token records its start position.
 * 2. Grammar precedence & grouping: Parser uses function calls where each level handles lower precedence operators.
 *     (exprs() does +- , term() does * and /, power() does **),Because higher precedence operators are parsed deeper in the call stack,
 *     they bind tighter (so 2+3*4 = 14). For **, parse_power() recursively calls itself for the
 *     right operand, which groups it right-to-left: 2**3**2 = 2**(3**2) = 512.
 * 3. Error positions:
 *    - Syntax errors: Reported at the start of offending token.
 *    - Missing operand & missing ')' at end of line: Reported at '\n' (or file_size + 1).
 *    - Division by zero & Negative integer exponent: Reported at start position of right operand expression.
 *    - Float NaN or Infinity: Reported at the operator position (** or /).
 * 4. Int vs Float arithmetic: Numbers with '.' are VAL_FLOAT, others VAL_INT. If any operand in an
 *    operation is VAL_FLOAT, both are promoted to double. Otherwise 64-bit integer arithmetic is used.
* 5. Large file performance: File read once into a single buffer then tokenizer/parser move index
*    pointers across it with no per-token allocation or string copies so execution moves on.
*/

// Data types

typedef enum {
    VAL_INT,
    VAL_FLOAT
} ValueType;

typedef struct {
    ValueType type;
    union {
        long long i;
        double f;
    };
} Value;

typedef enum {
    TOK_INT,
    TOK_FLOAT,
    TOK_PLUS,
    TOK_MINUS,
    TOK_STAR,
    TOK_SLASH,
    TOK_POW,
    TOK_LPAREN,
    TOK_RPAREN,
    TOK_EOL,
    TOK_ERROR
} TokenType;

typedef struct {
    TokenType type;
    size_t pos;
    union {
        long long val_i;
        double val_f;
    };
} Token;

typedef struct {
    const char *buffer;
    size_t size;
    size_t cursor;
    size_t current_pos;
    Token current_token;
    bool has_error;
    size_t error_pos;
} Parser;

typedef struct {
    char **lines;
    size_t count;
    size_t capacity;
} OutputList;

// Function declarations

static void init_output_list(OutputList *list);
static void append_output_line(OutputList *list, const char *line);
static void free_output_list(OutputList *list);

static Token get_next_token(Parser *p);
static void advance(Parser *p);
static void set_error(Parser *p, size_t pos);

static Value parse_expr(Parser *p);
static Value parse_term(Parser *p);
static Value parse_power(Parser *p);
static Value parse_primary(Parser *p);

static Value eval_add(Parser *p, Value a, Value b, size_t op_pos);
static Value eval_sub(Parser *p, Value a, Value b, size_t op_pos);
static Value eval_mul(Parser *p, Value a, Value b, size_t op_pos);
static Value eval_div(Parser *p, Value a, Value b, size_t op_pos, size_t right_pos);
static Value eval_pow(Parser *p, Value base, Value exp_val, size_t op_pos, size_t right_pos);

static bool process_file(const char *input_path, const char *output_path);
static void ensure_directory_exists(const char *dir_path);
static char *get_basename(const char *path);
static char *strip_txt_extension(const char *filename);
static int compare_strings(const void *a, const void *b);
static char *my_strdup(const char *s);

// Utilities

static char *my_strdup(const char *s) {
    if (!s) return NULL;
    size_t len = strlen(s) + 1;
    char *dup = (char *)malloc(len);
    if (dup) {
        memcpy(dup, s, len);
    }
    return dup;
}

static void ensure_directory_exists(const char *dir_path) {
    struct stat st;
    if (stat(dir_path, &st) == 0) {
        if (!S_ISDIR(st.st_mode)) {
            fprintf(stderr, "Error: Path '%s' exists but is not a directory.\n", dir_path);
            exit(1);
        }
    } else {
        if (mkdir(dir_path, 0755) != 0) {
            fprintf(stderr, "Error: failed to create directory '%s': %s\n", dir_path, strerror(errno));
            exit(1);
        }
    }
}

static char *get_basename(const char *path) {
    const char *slash1 = strrchr(path, '/');
    const char *slash2 = strrchr(path, '\\');
    const char *slash = slash1;
    if (slash2 != NULL && (slash == NULL || slash2 > slash)) {
        slash = slash2;
    }
    if (slash) {
        return my_strdup(slash + 1);
    }
    return my_strdup(path);
}

static char *strip_txt_extension(const char *filename) {
    size_t len = strlen(filename);
    if (len >= 4 && strcmp(filename + len - 4, ".txt") == 0) {
        char *base = (char *)malloc(len - 3);
        if (!base) exit(1);
        strncpy(base, filename, len - 4);
        base[len - 4] = '\0';
        return base;
    }
    return my_strdup(filename);
}

static int compare_strings(const void *a, const void *b) {
    return strcmp(*(const char **)a, *(const char **)b);
}

// Output list helpers

static void init_output_list(OutputList *list) {
    list->lines = NULL;
    list->count = 0;
    list->capacity = 0;
}

static void append_output_line(OutputList *list, const char *line) {
    if (list->count >= list->capacity) {
        size_t new_cap = (list->capacity == 0) ? 16 : list->capacity * 2;
        char **new_lines = (char **)realloc(list->lines, new_cap * sizeof(char *));
        if (!new_lines) {
            perror("realloc failed");
            exit(1);
        }
        list->lines = new_lines;
        list->capacity = new_cap;
    }
    list->lines[list->count] = my_strdup(line);
    if (!list->lines[list->count]) {
        perror("my_strdup failed");
        exit(1);
    }
    list->count++;
}

static void free_output_list(OutputList *list) {
    if (!list) return;
    for (size_t i = 0; i < list->count; i++) {
        free(list->lines[i]);
    }
    free(list->lines);
    list->lines = NULL;
    list->count = 0;
    list->capacity = 0;
}

// Lexer / Tokenizer

static Token get_next_token(Parser *p) {
    Token tok;
    tok.type = TOK_EOL;
    tok.pos = p->current_pos;
    tok.val_i = 0;
    tok.val_f = 0.0;

    // skip spaces
    while (p->cursor < p->size) {
        char c = p->buffer[p->cursor];
        if (c == ' ' || c == '\t' || c == '\r') {
            p->cursor++;
            p->current_pos++;
        } else {
            break;
        }
    }

    if (p->cursor >= p->size) {
        tok.type = TOK_EOL;
        tok.pos = p->current_pos;
        return tok;
    }

    char c = p->buffer[p->cursor];
    tok.pos = p->current_pos;

    if (c == '\n') {
        tok.type = TOK_EOL;
        return tok;
    }

    if (c == '+') {
        p->cursor++; p->current_pos++;
        tok.type = TOK_PLUS;
        return tok;
    }
    if (c == '-') {
        p->cursor++; p->current_pos++;
        tok.type = TOK_MINUS;
        return tok;
    }
    if (c == '*') {
        p->cursor++; p->current_pos++;
        if (p->cursor < p->size && p->buffer[p->cursor] == '*') {
            p->cursor++; p->current_pos++;
            tok.type = TOK_POW;
        } else {
            tok.type = TOK_STAR;
        }
        return tok;
    }
    if (c == '/') {
        p->cursor++; p->current_pos++;
        tok.type = TOK_SLASH;
        return tok;
    }
    if (c == '(') {
        p->cursor++; p->current_pos++;
        tok.type = TOK_LPAREN;
        return tok;
    }
    if (c == ')') {
        p->cursor++; p->current_pos++;
        tok.type = TOK_RPAREN;
        return tok;
    }

    // Number parsing
    if (c >= '0' && c <= '9') {
        size_t start_cursor = p->cursor;
        size_t start_pos = p->current_pos;

        while (p->cursor < p->size && (p->buffer[p->cursor] >= '0' && p->buffer[p->cursor] <= '9')) {
            p->cursor++;
            p->current_pos++;
        }

        if (p->cursor < p->size && p->buffer[p->cursor] == '.') {
            size_t dot_pos = p->current_pos;
            p->cursor++;
            p->current_pos++;

            if (p->cursor < p->size && (p->buffer[p->cursor] >= '0' && p->buffer[p->cursor] <= '9')) {
                while (p->cursor < p->size && (p->buffer[p->cursor] >= '0' && p->buffer[p->cursor] <= '9')) {
                    p->cursor++;
                    p->current_pos++;
                }

                if (p->cursor < p->size) {
                    char next_c = p->buffer[p->cursor];
                    if (isalpha((unsigned char)next_c) || next_c == '_' || next_c == '.') {
                        tok.type = TOK_ERROR;
                        tok.pos = p->current_pos;
                        p->cursor++;
                        p->current_pos++;
                        return tok;
                    }
                }

                char num_str[128];
                size_t len = p->cursor - start_cursor;

                if (len >= sizeof(num_str)) len = sizeof(num_str) - 1;
                memcpy(num_str, &p->buffer[start_cursor], len);
                num_str[len] = '\0';
                tok.type = TOK_FLOAT;
                tok.val_f = strtod(num_str, NULL);
                tok.pos = start_pos;
                return tok;
            } else {
                tok.type = TOK_ERROR;
                tok.pos = dot_pos;
                return tok;
            }
        } else {
            if (p->cursor < p->size) {
                char next_c = p->buffer[p->cursor];
                if (isalpha((unsigned char)next_c) || next_c == '_') {
                    tok.type = TOK_ERROR;
                    tok.pos = p->current_pos;
                    p->cursor++;
                    p->current_pos++;
                    return tok;
                }
            }

            char num_str[128];
            size_t len = p->cursor - start_cursor;

            if (len >= sizeof(num_str)) len = sizeof(num_str) - 1;
            memcpy(num_str, &p->buffer[start_cursor], len);
            num_str[len] = '\0';
            tok.type = TOK_INT;
            tok.val_i = strtoll(num_str, NULL, 10);
            tok.pos = start_pos;
            return tok;
        }
    }

    if (c == '.') {
        tok.type = TOK_ERROR;
        tok.pos = p->current_pos;
        p->cursor++;
        p->current_pos++;
        return tok;
    }

    tok.type = TOK_ERROR;
    tok.pos = p->current_pos;
    p->cursor++;
    p->current_pos++;
    return tok;
}

static void advance(Parser *p) {
    p->current_token = get_next_token(p);
}

static void set_error(Parser *p, size_t pos) {
    if (!p->has_error) {
        p->has_error = true;
        p->error_pos = pos;
    }
}

// Operators evaluation

static Value eval_add(Parser *p, Value a, Value b, size_t op_pos) {
    Value res;
    if (a.type == VAL_INT && b.type == VAL_INT) {
        res.type = VAL_INT;
        res.i = a.i + b.i;
    } else {
        res.type = VAL_FLOAT;
        double da = (a.type == VAL_FLOAT) ? a.f : (double)a.i;
        double db = (b.type == VAL_FLOAT) ? b.f : (double)b.i;
        res.f = da + db;
        if (isnan(res.f) || isinf(res.f)) {
            set_error(p, op_pos);
        }
    }
    return res;
}

static Value eval_sub(Parser *p, Value a, Value b, size_t op_pos) {
    Value res;
    if (a.type == VAL_INT && b.type == VAL_INT) {
        res.type = VAL_INT;
        res.i = a.i - b.i;
    } else {
        res.type = VAL_FLOAT;
        double da = (a.type == VAL_FLOAT) ? a.f : (double)a.i;
        double db = (b.type == VAL_FLOAT) ? b.f : (double)b.i;
        res.f = da - db;
        if (isnan(res.f) || isinf(res.f)) {
            set_error(p, op_pos);
        }
    }
    return res;
}

static Value eval_mul(Parser *p, Value a, Value b, size_t op_pos) {
    Value res;
    if (a.type == VAL_INT && b.type == VAL_INT) {
        res.type = VAL_INT;
        res.i = a.i * b.i;
    } else {
        res.type = VAL_FLOAT;
        double da = (a.type == VAL_FLOAT) ? a.f : (double)a.i;
        double db = (b.type == VAL_FLOAT) ? b.f : (double)b.i;
        res.f = da * db;
        if (isnan(res.f) || isinf(res.f)) {
            set_error(p, op_pos);
        }
    }
    return res;
}

static Value eval_div(Parser *p, Value a, Value b, size_t op_pos, size_t right_pos) {
    Value res = { .type = VAL_INT, .i = 0 };

    if ((b.type == VAL_INT && b.i == 0) || (b.type == VAL_FLOAT && b.f == 0.0)) {
        set_error(p, right_pos);
        return res;
    }

    if (a.type == VAL_INT && b.type == VAL_INT) {
        res.type = VAL_INT;
        res.i = a.i / b.i;
    } else {
        res.type = VAL_FLOAT;
        double da = (a.type == VAL_FLOAT) ? a.f : (double)a.i;
        double db = (b.type == VAL_FLOAT) ? b.f : (double)b.i;
        res.f = da / db;
        if (isnan(res.f) || isinf(res.f)) {
            set_error(p, op_pos);
        }
    }
    return res;
}

static Value eval_pow(Parser *p, Value base, Value exp_val, size_t op_pos, size_t right_pos) {
    Value res = { .type = VAL_INT, .i = 0 };

    if (base.type == VAL_INT && exp_val.type == VAL_INT) {
        if (exp_val.i < 0) {
            set_error(p, right_pos);
            return res;
        }
        res.type = VAL_INT;
        if (exp_val.i == 0) {
            res.i = 1LL;
        } else {
            long long b = base.i;
            long long e = exp_val.i;
            long long ans = 1;
            while (e > 0) {
                if (e % 2 == 1) ans *= b;
                b *= b;
                e /= 2;
            }
            res.i = ans;
        }
    } else {
        res.type = VAL_FLOAT;
        double db = (base.type == VAL_FLOAT) ? base.f : (double)base.i;
        double de = (exp_val.type == VAL_FLOAT) ? exp_val.f : (double)exp_val.i;
        res.f = pow(db, de);
        if (isnan(res.f) || isinf(res.f)) {
            set_error(p, op_pos);
        }
    }
    return res;
}

// Recursive parser

static Value parse_primary(Parser *p) {
    Value val = { .type = VAL_INT, .i = 0 };
    if (p->has_error) return val;

    if (p->current_token.type == TOK_INT) {
        val.type = VAL_INT;
        val.i = p->current_token.val_i;
        advance(p);
        return val;
    } else if (p->current_token.type == TOK_FLOAT) {
        val.type = VAL_FLOAT;
        val.f = p->current_token.val_f;
        advance(p);
        return val;
    } else if (p->current_token.type == TOK_LPAREN) {
        advance(p);
        val = parse_expr(p);
        if (p->has_error) return val;

        if (p->current_token.type == TOK_RPAREN) {
            advance(p);
            return val;
        } else {
            set_error(p, p->current_token.pos);
            return val;
        }
    } else {
        set_error(p, p->current_token.pos);
        return val;
    }
}

static Value parse_power(Parser *p) {
    Value left = parse_primary(p);
    if (p->has_error) return left;

    if (p->current_token.type == TOK_POW) {
        size_t op_pos = p->current_token.pos;
        advance(p);
        size_t right_pos = p->current_token.pos;
        Value right = parse_power(p);
        if (p->has_error) return left;
        return eval_pow(p, left, right, op_pos, right_pos);
    }

    return left;
}

static Value parse_term(Parser *p) {
    Value left = parse_power(p);
    if (p->has_error) return left;

    while (p->current_token.type == TOK_STAR || p->current_token.type == TOK_SLASH) {
        TokenType op = p->current_token.type;
        size_t op_pos = p->current_token.pos;
        advance(p);
        size_t right_pos = p->current_token.pos;
        Value right = parse_power(p);
        if (p->has_error) return left;

        if (op == TOK_STAR) {
            left = eval_mul(p, left, right, op_pos);
        } else {
            left = eval_div(p, left, right, op_pos, right_pos);
        }
        if (p->has_error) return left;
    }

    return left;
}

static Value parse_expr(Parser *p) {
    Value left = parse_term(p);
    if (p->has_error) return left;

    while (p->current_token.type == TOK_PLUS || p->current_token.type == TOK_MINUS) {
        TokenType op = p->current_token.type;
        size_t op_pos = p->current_token.pos;
        advance(p);
        Value right = parse_term(p);
        if (p->has_error) return left;

        if (op == TOK_PLUS) {
            left = eval_add(p, left, right, op_pos);
        } else {
            left = eval_sub(p, left, right, op_pos);
        }
        if (p->has_error) return left;
    }

    return left;
}

// File handling

static bool process_file(const char *input_path, const char *output_path) {
    FILE *fin = fopen(input_path, "rb");
    if (!fin) {
        fprintf(stderr, "Error: cannot open input file '%s': %s\n", input_path, strerror(errno));
        return false;
    }

    fseek(fin, 0, SEEK_END);
    long fsize_long = ftell(fin);
    fseek(fin, 0, SEEK_SET);

    if (fsize_long < 0) {
        fclose(fin);
        fprintf(stderr, "Error reading file size '%s'\n", input_path);
        return false;
    }

    size_t fsize = (size_t)fsize_long;
    char *buffer = (char *)malloc(fsize + 1);
    if (!buffer) {
        fclose(fin);
        fprintf(stderr, "Error: out of memory\n");
        return false;
    }

    if (fsize > 0 && fread(buffer, 1, fsize, fin) != fsize) {
        free(buffer);
        fclose(fin);
        fprintf(stderr, "Error reading file content from '%s'\n", input_path);
        return false;
    }
    fclose(fin);
    buffer[fsize] = '\0';

    OutputList out_list;
    init_output_list(&out_list);

    bool file_has_error = false;
    size_t global_error_pos = 0;

    size_t cursor = 0;
    size_t current_pos = 1;

    while (cursor < fsize) {
        size_t line_start_cursor = cursor;
        size_t line_start_pos = current_pos;

        size_t line_end_cursor = line_start_cursor;
        while (line_end_cursor < fsize && buffer[line_end_cursor] != '\n') {
            line_end_cursor++;
        }

        bool is_blank = true;
        bool is_comment = false;

        for (size_t i = line_start_cursor; i < line_end_cursor; i++) {
            char c = buffer[i];
            if (c != ' ' && c != '\t' && c != '\r') {
                is_blank = false;
                if (c == '#') {
                    is_comment = true;
                }
                break;
            }
        }

        if (is_blank || is_comment) {
            cursor = line_end_cursor;
            current_pos = line_start_pos + (line_end_cursor - line_start_cursor);
            if (cursor < fsize && buffer[cursor] == '\n') {
                cursor++;
                current_pos++;
            }
            continue;
        }

        Parser p;
        p.buffer = buffer;
        p.size = line_end_cursor;
        p.cursor = line_start_cursor;
        p.current_pos = line_start_pos;
        p.has_error = false;
        p.error_pos = 0;

        advance(&p);
        Value result = parse_expr(&p);

        if (!p.has_error && p.current_token.type != TOK_EOL) {
            set_error(&p, p.current_token.pos);
        }

        if (p.has_error) {
            file_has_error = true;
            global_error_pos = p.error_pos;
            break;
        }

        char line_out[128];
        if (result.type == VAL_INT) {
            snprintf(line_out, sizeof(line_out), "%lld\n", result.i);
        } else {
            snprintf(line_out, sizeof(line_out), "%.15g\n", result.f);
        }
        append_output_line(&out_list, line_out);

        cursor = line_end_cursor;
        current_pos = line_start_pos + (line_end_cursor - line_start_cursor);
        if (cursor < fsize && buffer[cursor] == '\n') {
            cursor++;
            current_pos++;
        }
    }

    free(buffer);

    FILE *fout = fopen(output_path, "wb");
    if (!fout) {
        fprintf(stderr, "Error: cannot open output file '%s': %s\n", output_path, strerror(errno));
        free_output_list(&out_list);
        return false;
    }

    if (file_has_error) {
        fprintf(fout, "ERROR:%zu\n", global_error_pos);
    } else {
        for (size_t i = 0; i < out_list.count; i++) {
            fputs(out_list.lines[i], fout);
        }
    }

    fclose(fout);
    free_output_list(&out_list);
    return true;
}

// Main

int main(int argc, char **argv) {
    const char *dir_arg = NULL;
    const char *outdir_arg = NULL;
    const char *input_file_arg = NULL;

    for (int i = 1; i < argc; i++) {
        if (strcmp(argv[i], "-d") == 0 || strcmp(argv[i], "--dir") == 0) {
            if (i + 1 < argc) {
                dir_arg = argv[++i];
            } else {
                fprintf(stderr, "Error: Missing argument for %s\n", argv[i]);
                return 1;
            }
        } else if (strcmp(argv[i], "-o") == 0 || strcmp(argv[i], "--output-dir") == 0) {
            if (i + 1 < argc) {
                outdir_arg = argv[++i];
            } else {
                fprintf(stderr, "Error: Missing argument for %s\n", argv[i]);
                return 1;
            }
        } else if (argv[i][0] == '-') {
            fprintf(stderr, "Error: Unknown option '%s'\n", argv[i]);
            return 1;
        } else {
            if (input_file_arg == NULL) {
                input_file_arg = argv[i];
            } else {
                fprintf(stderr, "Error: Unexpected argument '%s'\n", argv[i]);
                return 1;
            }
        }
    }

    if (!dir_arg && !input_file_arg) {
        fprintf(stderr, "Usage: calc [-d DIR | --dir DIR] [-o OUTDIR | --output-dir OUTDIR] [input.txt]\n");
        return 1;
    }

    if (dir_arg && input_file_arg) {
        fprintf(stderr, "Error: Cannot specify both -d DIR and an explicit input file.\n");
        return 1;
    }

    if (input_file_arg) {
        char *input_filename_base = get_basename(input_file_arg);
        char *stripped_name = strip_txt_extension(input_filename_base);

        char default_outdir[512];
        const char *actual_outdir = outdir_arg;
        if (!actual_outdir) {
            snprintf(default_outdir, sizeof(default_outdir), "%s_%s_%s", stripped_name, STUDENT_NAME, STUDENT_ID);
            actual_outdir = default_outdir;
        }

        ensure_directory_exists(actual_outdir);

        char out_filename[512];
        snprintf(out_filename, sizeof(out_filename), "%s/%s_%s_%s_%s.txt",
                 actual_outdir, stripped_name, STUDENT_NAME, STUDENT_LASTNAME, STUDENT_ID);

        bool success = process_file(input_file_arg, out_filename);

        free(input_filename_base);
        free(stripped_name);
        return success ? 0 : 1;
    }

    if (dir_arg) {
        DIR *dir = opendir(dir_arg);
        if (!dir) {
            fprintf(stderr, "Error: Cannot open directory '%s': %s\n", dir_arg, strerror(errno));
            return 1;
        }

        char *dir_base = get_basename(dir_arg);
        size_t dlen = strlen(dir_base);
        if (dlen > 0 && (dir_base[dlen - 1] == '/' || dir_base[dlen - 1] == '\\')) {
            dir_base[dlen - 1] = '\0';
        }

        char default_outdir[512];
        const char *actual_outdir = outdir_arg;
        if (!actual_outdir) {
            snprintf(default_outdir, sizeof(default_outdir), "%s_%s_%s", dir_base, STUDENT_NAME, STUDENT_ID);
            actual_outdir = default_outdir;
        }

        ensure_directory_exists(actual_outdir);

        struct dirent *entry;
        char **txt_files = NULL;
        size_t count = 0;
        size_t cap = 0;

        while ((entry = readdir(dir)) != NULL) {
            if (strcmp(entry->d_name, ".") == 0 || strcmp(entry->d_name, "..") == 0) {
                continue;
            }

            char full_entry_path[1024];
            snprintf(full_entry_path, sizeof(full_entry_path), "%s/%s", dir_arg, entry->d_name);

            struct stat st;
            if (stat(full_entry_path, &st) == 0 && S_ISREG(st.st_mode)) {
                size_t nlen = strlen(entry->d_name);
                if (nlen >= 4 && strcmp(entry->d_name + nlen - 4, ".txt") == 0) {
                    if (count >= cap) {
                        cap = (cap == 0) ? 16 : cap * 2;
                        txt_files = (char **)realloc(txt_files, cap * sizeof(char *));
                        if (!txt_files) exit(1);
                    }
                    txt_files[count++] = my_strdup(entry->d_name);
                }
            }
        }
        closedir(dir);

        if (count > 0) {
            qsort(txt_files, count, sizeof(char *), compare_strings);
        }

        bool all_success = true;
        for (size_t i = 0; i < count; i++) {
            char in_path[1024];
            snprintf(in_path, sizeof(in_path), "%s/%s", dir_arg, txt_files[i]);

            char *stripped = strip_txt_extension(txt_files[i]);
            char out_path[1024];
            snprintf(out_path, sizeof(out_path), "%s/%s_%s_%s_%s.txt",
                     actual_outdir, stripped, STUDENT_NAME, STUDENT_LASTNAME, STUDENT_ID);

            if (!process_file(in_path, out_path)) {
                all_success = false;
            }

            free(stripped);
            free(txt_files[i]);
        }
        free(txt_files);
        free(dir_base);

        return all_success ? 0 : 1;
    }

    return 0;
}