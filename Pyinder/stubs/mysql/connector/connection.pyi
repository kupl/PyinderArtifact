# Copyright (c) Meta Platforms, Inc. and affiliates.
#
# This source code is licensed under the MIT license found in the
# LICENSE file in the root directory of this source tree.

from __future__ import annotations

from typing import Any, Optional

from mysql.connector.abstracts import (
    MySQLConnectionAbstract as MySQLConnectionAbstract,
    MySQLCursorAbstract as MySQLCursorAbstract,
)

class MySQLConnection(MySQLConnectionAbstract):
    def __init__(self, *args: Any, **kwargs: Any) -> None: ...
    def shutdown(self) -> None: ...
    def close(self) -> None: ...
    disconnect: Any = ...
    @property
    def in_transaction(self): ...
    def get_row(self, binary: bool = ..., columns: Optional[Any] = ...): ...
    def get_rows(
        self,
        count: Optional[Any] = ...,
        binary: Optional[bool] = ...,
        columns: Optional[Any] = ...,
    ) -> Any: ...
    def consume_results(self) -> None: ...
    def cmd_init_db(self, database: Any): ...
    def cmd_query(
        self,
        query: Any,
        raw: bool = ...,
        buffered: bool = ...,
        raw_as_string: bool = ...,
    ) -> Any: ...
    def cmd_query_iter(self, statements: Any) -> None: ...
    def cmd_refresh(self, options: Any): ...
    def cmd_quit(self): ...
    def cmd_shutdown(self, shutdown_type: Optional[Any] = ...): ...
    def cmd_statistics(self): ...
    def cmd_process_kill(self, mysql_pid: Any): ...
    def cmd_debug(self): ...
    def cmd_ping(self): ...
    def cmd_change_user(
        self,
        username: str = ...,
        password: str = ...,
        database: str = ...,
        charset: int = ...,
    ): ...
    @property
    def database(self) -> MySQLConnection: ...
    @database.setter
    def database(self, value: Any) -> MySQLConnection: ...
    def is_connected(self): ...
    def reset_session(
        self,
        user_variables: Optional[Any] = ...,
        session_variables: Optional[Any] = ...,
    ) -> None: ...
    def reconnect(self, attempts: int = ..., delay: int = ...) -> None: ...
    def ping(
        self, reconnect: bool = ..., attempts: int = ..., delay: int = ...
    ) -> None: ...
    @property
    def connection_id(self): ...
    def cursor(
        self,
        buffered: Optional[Any] = ...,
        raw: Optional[Any] = ...,
        prepared: Optional[Any] = ...,
        cursor_class: Optional[Any] = ...,
        dictionary: Optional[Any] = ...,
        named_tuple: Optional[Any] = ...,
    ) -> MySQLCursorAbstract: ...
    def commit(self) -> None: ...
    def rollback(self) -> None: ...
    def info_query(self, query: Any): ...
    def cmd_stmt_prepare(self, statement: Any): ...
    def cmd_stmt_execute(
        self,
        statement_id: Any,
        data: Any = ...,
        parameters: Any = ...,
        flags: int = ...,
    ): ...
    def cmd_stmt_close(self, statement_id: Any) -> None: ...
    def cmd_stmt_send_long_data(self, statement_id: Any, param_id: Any, data: Any): ...
    def cmd_stmt_reset(self, statement_id: Any) -> None: ...
    def cmd_reset_connection(self) -> None: ...
    def handle_unread_result(self) -> None: ...
